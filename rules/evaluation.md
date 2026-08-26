# Stage 2 Evaluation Setup

> Official host and sandbox spec: **[Official Evaluation Spec](https://playground.sair.foundation/playground/mathematics-distillation-challenge-equational-theories-stage2/official-evaluation-spec)**. Questions on the [SAIR Foundation Zulip](https://zulip.sair.foundation/).

This page specifies how Stage 2 submissions are evaluated: submission format, solver environment, budget, scoring, proof policy, and the evaluation model.

For the high-level task description, key dates, and participation policy, see **[overview.md](overview.md)**.

## Submission Format

A Stage 2 submission is **a single Python file**.

| File | Purpose | Size limit |
|------|---------|------------|
| `solver.py` | The solving program for both tracks. Must contain all solving logic, including any prompt text as an in-file constant. The I/O protocol depends on the track (see below). | **500 KB** |

The solver is a free-form Python program. No required function signatures — the only requirement is following the I/O protocol of the chosen track.

If the solver uses LLM calls in **Solo**, it declares its prompt template as a top-level `PROMPT = "..."` string literal; the proxy extracts it via static AST parsing (the module is never imported or executed on the host), fills `{placeholder}` variables, and queries the LLM. In **Marathon**, the solver makes LLM calls itself via the helper `from marathon_llm import call_llm` (or any OpenAI-SDK call) against a local HTTP proxy; no template extraction.

## Submission Note

A solver that includes compressed data or binary blobs must disclose them in a submission note (plain text or Markdown, submitted alongside `solver.py`): what they contain, and the methodology used to generate them. Participants can add links to any open-source code used to generate or process them. Solvers without such payloads do not need a note.

The note is not machine-checked and does not affect judge verdicts — see [Human-Interpretable Artifacts](overview.md#human-interpretable-artifacts).

## Tracks

Stage 2 has two tracks. Both share the same judge, the same five-status verdict mapping, and the same single-file `solver.py` contract (≤ 500 KB). They differ only in I/O shape and budgeting:

| Track | Workload per process | Budget | I/O |
|-------|----------------------|--------|-----|
| **Solo** | One problem per solver subprocess | Fixed per-problem | stdin (problem JSON) / stdout (answer JSON) |
| **Marathon** | N problems per solver subprocess (reference N=100) | Single global budget = `N × 5 minutes` wall-clock, `N × 32768` tokens | manifest JSONL in / append-only JSONL out |

One solver source can support both. Full specs: `docs/solo_mode.md` and `docs/marathon_mode.md` in the repository.

## Solver Environment

The solver runs in an isolated subprocess:

- **No secrets**: no inherited API keys or environment variables beyond a minimal allowlist (`PATH`, `HOME`, `LANG`, etc.)
- **No direct network**: the internet is reachable only through the organizer-provided proxy
- **LLM access**: through the proxy — Solo via stdin/stdout JSON, Marathon via a local-only HTTP endpoint that authenticates with a per-run shared secret and meters tokens against the global budget
- **Judge access**: through the proxy — Solo via stdin/stdout JSON, Marathon via append-only JSONL output that the runner scores at end of run

```
Solver (subprocess) <--track-specific protocol--> Proxy <---> Judge (Lean verification)
                                                        <---> LLM (OpenAI-compatible API)
```

## Solver Budget

Reference values in `pipeline/config.json`. Numbers may still be tuned during Stage 2 based on community feedback.

**Solo (per problem):**

| Resource | Reference value | Notes |
|----------|-----------------|-------|
| Wall-clock timeout | 3600 seconds | Excludes organizer-side LLM latency. |
| LLM max output tokens per call | 65536 | Per-call cap on the LLM response length. |
| Submitted Lean code | 100 KB | Per-call code size cap. |

**Marathon (per run, N problems):**

The global budget is a flat per-problem allowance × N:

| Resource | Formula | Default at N=100 |
|----------|---------|------------------|
| Wall-clock | `N × 300 s` (5 minutes per problem) | 30 000 s (≈8.3 h) |
| Tokens | `N × 32768` | ~3.3 M |

The per-problem allowance is deliberately far below Solo's (300 s vs 3600 s wall-clock) — the solver cannot give every problem a Solo-depth attempt and must triage.

The solver manages its own pacing within the budget. Deterministic strategies cost no tokens. Exceeding the wall-clock or token budget terminates the solver.

## Answer Format

For each problem, the solver submits a proof certificate via a judge call:

```json
{"call": "judge", "verdict": "true", "code": "<Lean code>"}
```

or

```json
{"call": "judge", "verdict": "false", "code": "<Lean code>"}
```

- **True certificate**: a Lean 4 proof that the hypothesis equation implies the goal equation.
- **False certificate**: a Lean 4 proof that there exists a magma satisfying the hypothesis but not the goal. The carrier may be finite (e.g. an explicit operation table on `Fin n`) or infinite (e.g. `Nat` or a submission-defined inductive type) — the judge's goal is `∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G`, with no finiteness constraint.

Both are verified by the deterministic Lean judge. The judge returns exactly one of the following statuses:

| Status | Meaning |
|--------|---------|
| `accepted` | Certificate verified successfully |
| `unparsed` | Raw JSON could not be parsed |
| `malformed` | JSON parsed but violates schema |
| `incomplete_proof` | Proof uses `sorry`, `admit`, or disallowed axioms/declarations |
| `incorrect` | Proof is structurally valid but does not verify in Lean |

A problem is solved when the judge returns `accepted`.

## Scoring

Scoring follows Stage 1. The evaluation set is split into four categories — **Normal**, **Hard**, **Extra Hard**, and **Order 5** — and every problem carries equal weight:

- `accepted` → **1 point**
- rejected or timed out → **0 points**

No partial credit, no probabilistic scoring, no LLM-as-judge.

Leaderboard eligibility requires a single self-contained `solver.py` (≤ 500 KB) evaluated with the official SAIR Stage 2 runner — full list in the [Official Evaluation Spec](https://playground.sair.foundation/playground/mathematics-distillation-challenge-equational-theories-stage2/official-evaluation-spec).

## Proof Policy

Proofs are verified with **Lean 4.33.1** and the matching **Mathlib 4.33.1** release
(Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`). The official Linux toolchain
links **GMP 6.3.0**; this is pinned because arbitrary-precision arithmetic is part of the
kernel's trusted base, and an older GMP is not equivalent even under the same Lean version.

**Version changeover.** Evaluation moved to this toolchain on 2026-08-26 (UTC), from
Lean 4.32.2 / Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`. Verdicts issued before that
date were produced under the previous toolchain and remain valid: the change was an upstream
kernel-hardening release, so it can only reject proofs that were never sound, never invalidate
a proof that was. Any submission may be re-verified under the current toolchain on request.

Submitted proofs are checked against a dependency policy:

- **Allowed trusted axioms**: `propext`, `Quot.sound`, `Classical.choice`
- **Allowed declarations**: configurable allowlist per problem (when specified)
- Proofs using `sorry`, `admit`, or disallowed axioms/declarations are rejected as `incomplete_proof`.

## Evaluation Model

Solver LLM calls are served through the organizer proxy against a fixed, pinned configuration:

| | |
|---|---|
| Models | `openai/gpt-oss-120b` (`reasoning_effort = low`), `google/gemma-4-31b-it` (reasoning disabled) |
| Route | OpenRouter, upstream provider pinned to DeepInfra |
| Fallback | disabled — no automatic provider switching |

Secrets and API keys are never exposed to the solver; all model access is mediated by the proxy.

## Evaluation Configuration

| Parameter | Value |
|-----------|-------|
| Temperature | `0.0` |
| Seed | `0` (deterministic sampling, where the provider supports it) |
| Max output tokens | 65 536 per call |

Host and sandbox spec: [Official Evaluation Spec](https://playground.sair.foundation/playground/mathematics-distillation-challenge-equational-theories-stage2/official-evaluation-spec).

## Evaluation Problem Sets

The organizer runs offline evaluation on a private set spanning the four categories above. **No Stage 2 evaluation problem is reused from Stage 1 or from any publicly available selected problem set.**

For development, participants can use:

- The public sets bundled here: `examples/problems/sample_{20,200}.json` and the four SAIR sets (`normal`, `hard1`, `hard2`, `hard3`).
- Problems from the Equational Theories Project.
- The Stage 1 evaluation problems — [SAIRfoundation/equational-theories-selected-problems](https://huggingface.co/datasets/SAIRfoundation/equational-theories-selected-problems) — for reference on difficulty and shape only; none of them appear in the Stage 2 evaluation set.

## Official Repository

The official GitHub repository for Stage 2:

- [https://github.com/SAIRcompetition/equational-theories-lean-stage2](https://github.com/SAIRcompetition/equational-theories-lean-stage2)

This repository includes:

- the evaluation pipeline (proxy, runner, judge)
- demo solvers organized by track under `examples/{solo,marathon}/demos/` (Solo: `baseline/`, `twophase/`, `opnorm/`; Marathon: `baseline/`, `triage/`, `fewshot/`)
- a step-by-step tutorial per track (`examples/solo/TUTORIAL.md`, `examples/marathon/TUTORIAL.md`)
- local testing support via `scripts/run_harness.py` (Solo) and `scripts/run_marathon_harness.py` (Marathon)

## Local Testing

The repository supports full local testing before submission. A typical workflow:

1. Run `bash scripts/setup.sh` (one-time environment setup).
2. Source the environment: `source .env.judge`.
3. Study the demo solvers (start with `examples/solo/demos/baseline/`) and read `examples/solo/TUTORIAL.md` for annotated walkthroughs. For the Marathon track, see `examples/marathon/TUTORIAL.md`.
4. Test your solver locally, for example:
   ```bash
   python3 -m pipeline.runner \
     --submission examples/solo/demos/baseline \
     --problems examples/problems/sample_20.json
   ```
5. Review results in `pipeline/results/`.
6. Iterate — improve deterministic strategies first, then refine your prompt.
7. Submit only after your solver is stable locally.
