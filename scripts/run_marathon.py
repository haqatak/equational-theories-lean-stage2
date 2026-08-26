"""
Marathon-mode CLI entry.

Usage:
    python3 scripts/run_marathon.py \\
        --solver examples/marathon/demos/baseline \\
        --manifest examples/problems/marathon/normal_100.jsonl

Defaults follow the reference in ``docs/marathon_mode.md``:
    * Wall-clock budget = N * 300 s   (5 minutes per problem)
    * Token budget      = N * 32768

The per-problem allowance is deliberately far below Solo's 3600 s /
65536 tokens: the solver cannot afford a Solo-depth attempt on every
problem and must triage. Override with explicit ``--budget-seconds`` /
``--budget-tokens`` for local experiments.

The Solo path (``scripts/run_harness.py`` / ``pipeline/runner.py``) is
unchanged. This script is the *only* CLI entry for marathon mode.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from pipeline.marathon_runner import run_marathon  # noqa: E402
from pipeline.marathon_score import score_marathon  # noqa: E402


# Marathon's global budget is a flat `N * per-problem` allowance —
# 5 minutes and 32768 tokens per problem, vs Solo's 60 minutes / 65536.
# The gap is what makes triage load-bearing: the solver cannot afford a
# Solo-depth attempt on every problem and must choose what to attempt.
PER_PROBLEM_SECONDS = 300
PER_PROBLEM_TOKENS = 32768


def _count_manifest_lines(path: Path) -> int:
    text = path.read_text(encoding="utf-8")
    stripped = text.lstrip()
    if not stripped:
        return 0
    if stripped[0] == "[":
        return len(json.loads(text))
    return sum(1 for line in text.splitlines() if line.strip())


def _default_paths(submission_dir: Path, manifest_path: Path) -> dict[str, Path]:
    run_id = time.strftime("%Y%m%d_%H%M%S")
    base = REPO_ROOT / "pipeline" / "results" / "marathon" / f"{submission_dir.name}__{manifest_path.stem}__{run_id}"
    return {
        "output": base / "answers.jsonl",
        "scratch": base / "scratch",
        "summary": base / "summary.json",
        "log": base / "run.log",
    }


def main() -> int:
    p = argparse.ArgumentParser(description="Run a marathon-mode evaluation")
    p.add_argument("--solver", required=True, help="Submission directory (single-file solver.py)")
    p.add_argument("--manifest", required=True, help="JSONL manifest of problems")
    p.add_argument("--budget-seconds", type=float, default=None,
                   help=f"Wall-clock budget. Default: N * {PER_PROBLEM_SECONDS}s")
    p.add_argument("--budget-tokens", type=int, default=None,
                   help=f"LLM token budget. Default: N * {PER_PROBLEM_TOKENS}")
    p.add_argument("--output-dir", default=None,
                   help="Run dir; default under pipeline/results/marathon/")
    p.add_argument("--no-score", action="store_true",
                   help="Run the solver but skip the score phase (debug).")
    p.add_argument("--score-only", action="store_true",
                   help="Skip the run phase; score the existing output file.")
    args = p.parse_args()

    submission_dir = Path(args.solver).resolve()
    manifest_path = Path(args.manifest).resolve()
    if not submission_dir.is_dir():
        print(f"error: --solver is not a directory: {submission_dir}", file=sys.stderr)
        return 2
    if not manifest_path.is_file():
        print(f"error: --manifest is not a file: {manifest_path}", file=sys.stderr)
        return 2

    n = _count_manifest_lines(manifest_path)
    if n == 0:
        print(f"error: empty manifest: {manifest_path}", file=sys.stderr)
        return 2

    if args.budget_seconds is None:
        args.budget_seconds = float(n * PER_PROBLEM_SECONDS)
    if args.budget_tokens is None:
        args.budget_tokens = n * PER_PROBLEM_TOKENS

    if args.output_dir:
        run_dir = Path(args.output_dir).resolve()
        paths = {
            "output": run_dir / "answers.jsonl",
            "scratch": run_dir / "scratch",
            "summary": run_dir / "summary.json",
            "log": run_dir / "run.log",
        }
    else:
        paths = _default_paths(submission_dir, manifest_path)
        run_dir = paths["output"].parent
    run_dir.mkdir(parents=True, exist_ok=True)

    print(f"Marathon Run")
    print(f"  Solver:       {submission_dir}")
    print(f"  Manifest:     {manifest_path} (N={n})")
    print(f"  Budget:       {int(args.budget_seconds)}s wall, {args.budget_tokens} tokens "
          f"({n} × {PER_PROBLEM_SECONDS}s / {n} × {PER_PROBLEM_TOKENS}tok)")
    print(f"  Run dir:      {run_dir}")
    print()

    log_fh = paths["log"].open("w", encoding="utf-8")
    try:
        run_result = None
        if not args.score_only:
            run_result = run_marathon(
                submission_dir=submission_dir,
                manifest_path=manifest_path,
                output_path=paths["output"],
                scratch_dir=paths["scratch"],
                budget_seconds=args.budget_seconds,
                budget_tokens=args.budget_tokens,
                log_stream=log_fh,
            )
            print(f"Solver exited rc={run_result.exit_code} "
                  f"wall={run_result.wall_seconds:.1f}s "
                  f"sigterm={run_result.sigterm_fired} sigkill={run_result.sigkill_fired}")
            if run_result.stderr_tail.strip():
                print(f"  (stderr tail in {paths['log']})")
        else:
            print(f"--score-only: scoring existing output at {paths['output']}")

        if args.no_score:
            print("--no-score: skipping verification phase")
            return 0

        summary = score_marathon(
            manifest_path=manifest_path,
            manifest_problems=(run_result.manifest_problems if run_result else None),
            # Pre-launch snapshots of the judge caps and proof policy (see
            # MarathonRunResult); --score-only has no tamper window and
            # resolves both fresh.
            judge_config=(run_result.judge_config if run_result else None),
            default_proof_policy=(run_result.proof_policy if run_result else None),
            output_path=paths["output"],
            wall_seconds=(run_result.wall_seconds if run_result else None),
            sigterm_fired=(run_result.sigterm_fired if run_result else False),
            sigkill_fired=(run_result.sigkill_fired if run_result else False),
            tokens_used=(run_result.tokens_used if run_result else None),
            tokens_exhausted=(run_result.tokens_exhausted if run_result else False),
            log_stream=log_fh,
        )
        paths["summary"].write_text(
            json.dumps(summary.to_dict(), indent=2, ensure_ascii=False)
        )

        print()
        print(f"=== Result ===")
        print(f"  Score:         {summary.score} / {n}")
        print(f"  Attempted:     {summary.attempted}")
        print(f"  Not attempted: {summary.not_attempted}")
        print(f"  By status:     {dict(summary.by_status)}")
        if summary.wall_seconds is not None:
            print(f"  Wall used:     {summary.wall_seconds:.1f}s "
                  f"of {int(args.budget_seconds)}s budget")
        if summary.tokens_used is not None:
            print(f"  Tokens used:   {summary.tokens_used} "
                  f"of {args.budget_tokens} budget"
                  + (" (exhausted)" if summary.tokens_exhausted else ""))
        print(f"  Summary:       {paths['summary']}")
        print(f"  Output:        {paths['output']}")
        print(f"  Log:           {paths['log']}")
    finally:
        log_fh.close()

    return 0


if __name__ == "__main__":
    sys.exit(main())
