"""
Proxy: launches a solver subprocess and mediates all I/O.

The solver communicates via stdin/stdout JSON messages.
The proxy forwards judge and llm requests, enforces budgets,
and records results.
"""
from __future__ import annotations

import ast
import json
import os
import subprocess
import sys
import threading
import time
import uuid
from pathlib import Path
from typing import Any, Callable

import openai
from openai import OpenAI

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from judge.verify import verify_answer

# Default proof policy
DEFAULT_PROOF_POLICY = {
    "allowed_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "allowed_declarations": ["letFun"],
    "allowed_declaration_prefixes": [
        "And.", "Bool.", "Classical.", "Decidable.", "Eq.",
        "EquationLHS", "EquationRHS", "Goal",
        "Exists.", "False.",
        "Fin.", "Fintype.", "Function.", "HEq.", "Iff.", "Init.", "Int.", "Lean.",
        "List.", "Magma.", "Mathlib.", "MemoFinOp.", "Nat.", "Nonempty.", "Not.",
        "NthRewrites.", "OfNat.", "Option.", "Or.", "Prod.", "PUnit.",
        "RewriteCombinations.", "RewriteGoal.", "RewriteHypothesis.",
        "RewriteHypothesisAndGoal.", "SimpleRewrites.",
        "Std.", "Subgraph.", "Subtype.", "Sum.",
        "Trans.", "True.", "Unit.",
        "JudgeDecide.", "JudgeFinOp.", "JudgeMagma.",
        "inst", "of_decide_", "submission.",
        "congrArg", "congr_arg", "eq_self", "of_eq_true", "id",
        "eq_comm", "eq_mp", "eq_mpr", "rfl", "absurd",
    ],
}

def load_config(config_path: str | Path | None = None) -> dict:
    """Load config.json, falling back to the default alongside this file."""
    if config_path is None:
        config_path = Path(__file__).parent / "config.json"
    return json.loads(Path(config_path).read_text())


def load_problems(problems_path: str | Path) -> list[dict]:
    """Load a problem set from disk.

    Accepts two formats — chosen by first non-whitespace character, not by
    filename extension, so a stray ``.txt`` or mis-named mirror still works:

    * **JSONL** (HuggingFace upstream format): one JSON object per line.
      ``SAIRfoundation/equational-theories-selected-problems`` publishes the
      four canonical sets this way; keeping the on-disk bytes identical to the
      Hub means ``datasets.load_dataset`` and ``wc -l`` both work.
    * **JSON array**: a single top-level ``[...]`` list. Used by the bundled
      samples ``examples/problems_{20,200}.json`` and any local conversion.

    Returns the decoded list of problem dicts. Raises ``ValueError`` with a
    caller-friendly message on malformed input.
    """
    path = Path(problems_path)
    text = path.read_text(encoding="utf-8")
    stripped = text.lstrip()
    if not stripped:
        raise ValueError(f"{path}: file is empty")
    if stripped[0] == "[":
        data = json.loads(text)
        if not isinstance(data, list):
            raise ValueError(f"{path}: expected JSON array at top level")
        return data
    problems: list[dict] = []
    for lineno, raw in enumerate(text.splitlines(), 1):
        if not raw.strip():
            continue
        try:
            value = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise ValueError(f"{path}:{lineno}: invalid JSONL ({exc})") from exc
        # A JSONL problem set is one record per line. A top-level wrapper like
        # ``{"problems": [...]}`` parses as one dict with no ``id`` field —
        # reject it here instead of letting it flow through as a fake problem.
        if not isinstance(value, dict) or "id" not in value:
            raise ValueError(
                f"{path}:{lineno}: expected a problem record (dict with 'id'), "
                f"got {type(value).__name__}"
            )
        problems.append(value)
    return problems


def _to_judge_problem(problem: dict) -> dict:
    """Translate problem to judge's format (HF-aligned)."""
    return {
        "id": problem["id"],
        "eq1_id": problem["eq1_id"],
        "eq2_id": problem["eq2_id"],
        "equation1": problem["equation1"],
        "equation2": problem["equation2"],
        "proof_policy": problem.get("proof_policy") or DEFAULT_PROOF_POLICY,
    }


def _call_judge(
    problem: dict,
    verdict: str,
    code: str,
    *,
    lean_timeout_seconds: int | None = None,
    max_code_length: int | None = None,
    max_false_cert_bytes: int | None = None,
) -> dict:
    """Call the judge and return a simplified result for the solver.

    ``lean_timeout_seconds`` lets the caller bound the Lean subprocess so a
    judge request issued near the wall-clock deadline cannot keep the proxy
    blocked well past it.

    ``max_code_length`` / ``max_false_cert_bytes`` propagate the judge size
    caps from the active pipeline config so the values advertised to the
    solver in the startup message are the same values the judge actually
    enforces.
    """
    from judge.verify import (
        JudgeConfig,
        JudgeConfigurationError,
        JudgeInfrastructureError,
        _resolve_config,
    )
    judge_problem = _to_judge_problem(problem)
    raw_answer = json.dumps({"verdict": verdict, "code": code})
    config = None
    if (
        lean_timeout_seconds is not None
        or max_code_length is not None
        or max_false_cert_bytes is not None
    ):
        base = _resolve_config(None)
        config = JudgeConfig(
            lake_bin=base.lake_bin,
            lean_bin=base.lean_bin,
            artifact_dir=base.artifact_dir,
            lean_timeout_seconds=(
                max(1, int(lean_timeout_seconds))
                if lean_timeout_seconds is not None
                else base.lean_timeout_seconds
            ),
            max_code_length=(
                int(max_code_length)
                if max_code_length is not None
                else base.max_code_length
            ),
            max_false_cert_bytes=(
                int(max_false_cert_bytes)
                if max_false_cert_bytes is not None
                else base.max_false_cert_bytes
            ),
        )
    try:
        result = verify_answer(judge_problem, raw_answer, config=config)
    except JudgeInfrastructureError as e:
        return {"error": f"judge infrastructure error: {e}"}
    except JudgeConfigurationError as e:
        # Organizer-side bad problem — fail closed rather than crashing the
        # whole evaluation run. This is an infra-class failure, not a
        # contestant verdict.
        return {"error": f"judge configuration error: {e}"}
    response: dict[str, Any] = {"status": result["status"]}
    if result.get("stderr"):
        response["stderr"] = result["stderr"]
    if result.get("message"):
        response["message"] = result["message"]
    return response


def _is_openrouter_base_url(base_url: str) -> bool:
    """True iff ``base_url`` points at the public OpenRouter API root.

    Matches ``openrouter.ai`` and any subdomain (e.g. a regional mirror),
    nothing else. Used to decide whether it's safe to emit OpenRouter-only
    ``extra_body`` fields — see ``_call_llm`` for the reasoning.
    """
    from urllib.parse import urlparse
    try:
        host = (urlparse(base_url).hostname or "").lower()
    except (ValueError, TypeError):
        return False
    return host == "openrouter.ai" or host.endswith(".openrouter.ai")


class UnknownModelError(ValueError):
    """Raised when a solver asks for a model outside the evaluation allowlist."""


def _resolve_model(llm_config: dict, requested: str | None) -> dict:
    """Pick the model entry to use, and its per-model routing fields.

    The evaluation pins more than one model, and ``provider`` /
    ``reasoning_effort`` differ per model — gpt-oss-120b runs at
    ``reasoning_effort = low`` while gemma has reasoning disabled — so they
    cannot be read from the flat ``llm.*`` keys once a solver selects a
    model. ``llm.models`` is the allowlist; the flat keys stay as the
    default so an existing config without ``models`` behaves unchanged.

    A solver may only name a model on the allowlist: an unpinned model
    would break the reproducibility the evaluation depends on.
    """
    default = {
        "model": llm_config["model"],
        "provider": llm_config.get("provider"),
        "reasoning_effort": llm_config.get("reasoning_effort"),
    }
    entries = llm_config.get("models")
    if not isinstance(entries, list) or not entries:
        if requested is not None and requested != default["model"]:
            raise UnknownModelError(requested)
        return default
    if requested is None:
        for entry in entries:
            if isinstance(entry, dict) and entry.get("model") == default["model"]:
                return {**default, **entry}
        return default
    for entry in entries:
        if isinstance(entry, dict) and entry.get("model") == requested:
            # reasoning_effort is absent for models with reasoning disabled;
            # falling back to the default's effort would silently re-enable it.
            return {
                "model": requested,
                "provider": entry.get("provider", default["provider"]),
                "reasoning_effort": entry.get("reasoning_effort"),
            }
    raise UnknownModelError(requested)


def _call_llm(
    prompt: str,
    config: dict,
    *,
    max_seconds: float | None = None,
    stream_chunk_hook: Callable[[str, str], None] | None = None,
    model: str | None = None,
) -> dict:
    """Call the LLM via the OpenAI SDK and return the response.

    Routing is driven by three optional ``llm.*`` config fields, so the
    same proxy talks to any OpenAI-compatible endpoint without code
    changes — DeepSeek, Kimi/Moonshot, GLM/Zhipu, Minimax, Qwen,
    api.openai.com, etc.:

    * ``base_url`` — API root. Default ``https://openrouter.ai/api/v1``.
    * ``api_key_env`` — name of the env var holding the key. Default
      falls back to ``OPENAI_API_KEY`` then ``OPENROUTER_API_KEY``.

    OpenRouter-specific extras (``provider`` routing hint, ``reasoning.effort``
    wrapper) are emitted only when ``base_url`` points at OpenRouter. The
    repo's default ``pipeline/config.json`` ships with ``provider`` and
    ``reasoning_effort`` populated; a maintainer who migrates to a direct
    provider by "add ``base_url`` + ``api_key_env``, don't touch the rest"
    gets the right behavior automatically — no OpenRouter private fields
    leak to DeepSeek / Kimi / GLM / Minimax / api.openai.com.

    Using the official SDK instead of raw ``requests.post`` fixes a real
    bug we hit: on long reasoning calls the OpenRouter proxy sometimes
    returns a multi-line body that ``resp.json()`` can't parse, and the
    SDK handles that edge case (SSE downgrade, partial JSON, ``reasoning``
    vs ``content`` split for reasoning models) in tested code we don't
    own.

    ``max_seconds`` clamps the HTTP timeout. The proxy passes the
    remaining wall-clock budget so a call near the deadline can't stall
    the whole problem for the full 300 s default.
    """
    llm_config = config["llm"]

    base_url = (
        llm_config.get("base_url")
        or os.environ.get("OPENAI_BASE_URL")
        or "https://openrouter.ai/api/v1"
    )

    api_key_env = llm_config.get("api_key_env")
    if api_key_env:
        api_key = os.environ.get(api_key_env, "")
        if not api_key:
            return {"error": f"{api_key_env} not set"}
    else:
        api_key = (
            os.environ.get("OPENAI_API_KEY")
            or os.environ.get("OPENROUTER_API_KEY")
            or ""
        )
        if not api_key:
            return {"error": "OPENAI_API_KEY or OPENROUTER_API_KEY not set"}

    # Default LLM HTTP budget is 300 s. Contestants running the official
    # pipeline don't need to touch this. Deep-mining scripts that raise
    # ``solver.timeout_seconds`` further (above the 3600 s reference) can
    # also raise ``llm.http_timeout_seconds`` so a slow reasoning chain on
    # hard problems has room to finish before the total-deadline cut-off
    # (see streaming deadline below). ``max_seconds`` — the solver's
    # remaining wall-clock budget — is always the hard upper bound.
    try:
        http_timeout = float(llm_config.get("http_timeout_seconds", 300.0))
    except (TypeError, ValueError):
        http_timeout = 300.0
    if max_seconds is not None:
        http_timeout = min(http_timeout, float(max_seconds))
    http_timeout = max(1.0, http_timeout)

    # ``extra_body`` carries OpenRouter-specific fields: the ``provider``
    # routing hint (picks the upstream inference backend) and the
    # ``reasoning.effort`` wrapper (OpenRouter's envelope for the OpenAI
    # reasoning-models knob). Both are gated on the base_url actually being
    # OpenRouter — because the repo's default ``pipeline/config.json`` ships
    # with ``provider`` and ``reasoning_effort`` populated, the most natural
    # migration to a direct provider is "add ``base_url`` + ``api_key_env``,
    # don't touch the rest". Emitting OpenRouter-only fields to DeepSeek /
    # Kimi / GLM / Minimax / api.openai.com would at best be silently ignored
    # and at worst 4xx — neither outcome matches the commit-message promise
    # that the same proxy talks to any OpenAI-compatible endpoint.
    chosen = _resolve_model(llm_config, model)

    extra_body: dict[str, Any] = {}
    if _is_openrouter_base_url(base_url):
        if chosen.get("provider"):
            extra_body["provider"] = {"order": [chosen["provider"]]}
        if chosen.get("reasoning_effort"):
            extra_body["reasoning"] = {"effort": chosen["reasoning_effort"]}

    client = OpenAI(api_key=api_key, base_url=base_url, timeout=http_timeout)

    kwargs: dict[str, Any] = {
        "model": chosen["model"],
        "messages": [{"role": "user", "content": prompt}],
        "max_tokens": llm_config["max_output_tokens"],
        "temperature": llm_config["temperature"],
    }
    if llm_config.get("use_seed") and "seed" in llm_config:
        kwargs["seed"] = llm_config["seed"]
    if extra_body:
        kwargs["extra_body"] = extra_body

    # When a chunk hook is supplied we ask the SDK to stream; the caller can
    # then watch ``reasoning`` and ``content`` deltas arrive in real time
    # (critical for high-reasoning models where a single non-streaming
    # response can take 5+ minutes of complete silence).
    if stream_chunk_hook is not None:
        kwargs["stream"] = True

    # ``http_timeout`` is a total-request budget here — the openai SDK's
    # ``timeout`` kwarg enforces it end-to-end, unlike raw ``requests`` where
    # ``timeout=N`` is per-socket-read idle and a slow-streaming reasoning
    # model can drip bytes for many minutes without tripping it.
    try:
        completion = client.chat.completions.create(**kwargs)
    except openai.APITimeoutError:
        return {"error": f"LLM request timed out ({http_timeout:.0f}s)"}
    except openai.APIError as e:
        return {"error": f"LLM API error: {e}"}
    except Exception as e:  # noqa: BLE001 — SDK raises many error shapes; don't hide
        return {"error": f"LLM call failed: {type(e).__name__}: {e}"}

    # ── Non-streaming path ─────────────────────────────────────────────
    if stream_chunk_hook is None:
        try:
            choice = completion.choices[0]
            message = choice.message
        except (AttributeError, IndexError, TypeError) as e:
            return {"error": f"LLM response parse error: {e}"}
        finish_reason = getattr(choice, "finish_reason", None)
        content = getattr(message, "content", None)
        truncated = False
        if not content:
            # OpenRouter exposes the reasoning trace under ``reasoning`` while
            # DeepSeek's direct API uses ``reasoning_content`` — fall back to
            # whichever the upstream populated. When the model spends its
            # entire token budget reasoning and emits no final answer
            # (finish_reason=length), the trace is the only signal we have.
            content = (
                getattr(message, "reasoning", None)
                or getattr(message, "reasoning_content", None)
                or ""
            )
            # Tell the solver the final answer was lost to token exhaustion
            # so it can adapt (raise max_output_tokens, shorten prompt) rather
            # than retrying the same shape and burning more budget.
            if finish_reason == "length":
                truncated = True
        response: dict[str, Any] = {"response": content}
        if truncated:
            response["truncated"] = True
        return response

    # ── Streaming path ────────────────────────────────────────────────
    # Forward each chunk to the hook as ``(kind, text)`` where ``kind`` is
    # "reasoning" or "content". Accumulate both; prefer ``content`` for the
    # final response (fall back to ``reasoning`` when the model ran out of
    # tokens mid-chain-of-thought, same policy as the non-streaming path).
    #
    # SDK's ``timeout`` is a per-chunk read deadline in streaming mode —
    # every arriving byte resets it. A slow-drip reasoning chain can
    # therefore dribble past ``http_timeout`` without ever tripping
    # APITimeoutError. Enforce a total-wallclock deadline here so the
    # streaming path is actually bounded end-to-end (observed in practice
    # on gpt-oss-120b reasoning_effort=high: 840s of trickled tokens past
    # a 300s nominal budget).
    reasoning_parts: list[str] = []
    content_parts: list[str] = []
    final_finish_reason: str | None = None
    stream_deadline = time.monotonic() + http_timeout
    try:
        for chunk in completion:
            if time.monotonic() >= stream_deadline:
                try:
                    completion.response.close()
                except Exception:  # noqa: BLE001 — close path varies across SDK versions
                    pass
                return {
                    "error": (
                        f"LLM request timed out ({http_timeout:.0f}s total, "
                        "streaming)"
                    )
                }
            try:
                choice = chunk.choices[0]
                delta = choice.delta
            except (AttributeError, IndexError, TypeError):
                continue
            # ``finish_reason`` arrives on the terminal chunk(s); capture
            # whichever value lands last so we know if the model ran out of
            # tokens before emitting a final answer.
            fr = getattr(choice, "finish_reason", None)
            if fr:
                final_finish_reason = fr
            # OpenRouter streams reasoning under ``delta.reasoning``; DeepSeek's
            # direct API streams it under ``delta.reasoning_content``. Capture
            # whichever the upstream emits so we can fall back to the trace
            # when the model exhausts its budget without a final answer.
            reasoning_piece = (
                getattr(delta, "reasoning", None)
                or getattr(delta, "reasoning_content", None)
            )
            if reasoning_piece:
                reasoning_parts.append(reasoning_piece)
                try:
                    stream_chunk_hook("reasoning", reasoning_piece)
                except Exception:  # noqa: BLE001
                    pass
            content_piece = getattr(delta, "content", None)
            if content_piece:
                content_parts.append(content_piece)
                try:
                    stream_chunk_hook("content", content_piece)
                except Exception:  # noqa: BLE001
                    pass
    except openai.APITimeoutError:
        return {"error": f"LLM request timed out ({http_timeout:.0f}s)"}
    except openai.APIError as e:
        return {"error": f"LLM API error: {e}"}

    full_content = "".join(content_parts)
    truncated = False
    if not full_content:
        full_content = "".join(reasoning_parts)
        # Same policy as the non-streaming path: when the final answer is
        # empty and the model stopped because it hit max_tokens, the response
        # was truncated. Surface that to the solver.
        if final_finish_reason == "length":
            truncated = True
    response: dict[str, Any] = {"response": full_content}
    if truncated:
        response["truncated"] = True
    return response


def _extract_prompt_from_solver(solver_path: Path) -> str:
    """Extract top-level `PROMPT = "..."` string literal from solver.py via AST.

    Parsing only — never executes the solver module, so it's safe even for
    untrusted contestant code. Returns "" if PROMPT is absent or is not a
    simple string literal (f-strings, concatenation, etc. are not supported).
    """
    try:
        source = solver_path.read_text(encoding="utf-8")
        tree = ast.parse(source)
    except (OSError, SyntaxError, UnicodeDecodeError, ValueError):
        # ValueError: ast.parse rejects sources containing NUL bytes.
        return ""
    for node in tree.body:
        if not isinstance(node, ast.Assign):
            continue
        if len(node.targets) != 1:
            continue
        target = node.targets[0]
        if not (isinstance(target, ast.Name) and target.id == "PROMPT"):
            continue
        value = node.value
        if isinstance(value, ast.Constant) and isinstance(value.value, str):
            return value.value
        return ""
    return ""


DEFAULT_SANDBOX_CONFIG: dict[str, Any] = {"mode": "none"}

# Per-line cap on solver stdout. Any protocol message (judge call with a full
# Lean proof, LLM context, etc.) comfortably fits in a fraction of a MiB, so 1
# MiB is generous for legitimate use. Without this cap, a hostile solver could
# write a huge line with no newline and exhaust proxy memory inside readline.
MAX_STDOUT_LINE_CHARS = 1 * 1024 * 1024

# Tail of solver stderr to retain. Bounded so a flood-stderr solver can't
# exhaust proxy memory. 64 KiB is enough for a handful of Python tracebacks
# — the diagnostic case this exists for.
MAX_STDERR_TAIL_CHARS = 64 * 1024


def _solver_subprocess_env(
    sandbox_cfg: dict[str, Any], solver_env: dict[str, str]
) -> dict[str, str] | None:
    """Env to pass into subprocess.Popen when launching the solver.

    mode=none   : the Popen child is the solver itself → hand it the stripped
                  ``solver_env`` (minimal allowlist, no secrets).
    mode=docker : the Popen child is the host ``docker`` CLI, which needs
                  DOCKER_HOST / DOCKER_CONFIG / DOCKER_CERT_PATH / TLS vars to
                  reach the daemon. Return ``None`` so Popen inherits the host
                  env. Container-visible env is controlled separately via the
                  explicit ``-e`` flags in argv.
    """
    if sandbox_cfg.get("mode", "none") == "docker":
        return None
    return solver_env


def _build_solver_argv(
    submission_dir: Path, sandbox_cfg: dict[str, Any]
) -> tuple[list[str], str | None, str | None]:
    """Return (argv, cwd, container_name) for launching the solver.

    Mode "none": legacy path, runs solver.py as a host subprocess under
    the submission directory. ``container_name`` is ``None``.

    Mode "docker": runs solver.py inside a container with the submission
    directory bind-mounted read-only. Hardened with --network=none,
    --read-only, cpu/memory/pids limits, and a small tmpfs for /tmp so
    Python can still start. ``container_name`` is a unique id injected
    via ``--name``; the caller uses it to ``docker kill`` the container
    if the host docker CLI is terminated (e.g. watchdog timeout) so the
    container does not outlive the proxy.
    """
    mode = sandbox_cfg.get("mode", "none")
    if mode == "none":
        return [sys.executable, "solver.py"], str(submission_dir.resolve()), None
    if mode == "docker":
        image = sandbox_cfg.get("image", "ee-solver:latest")
        memory = f"{int(sandbox_cfg.get('memory_mb', 512))}m"
        cpus = str(sandbox_cfg.get("cpus", 1))
        pids = str(int(sandbox_cfg.get("pids_limit", 64)))
        tmpfs_size = f"{int(sandbox_cfg.get('tmpfs_size_mb', 16))}m"
        container_name = f"ee-solver-{uuid.uuid4().hex[:16]}"
        argv = [
            "docker", "run", "--rm", "-i",
            "--name", container_name,
            # Defense in depth: ``USER solver`` (uid 1000) is set in the
            # Dockerfile, but a degraded image (missing the RUN useradd,
            # wrong tag) would otherwise start as root. Pin uid:gid here
            # so the sandbox stays non-root even if the image regresses.
            "--user", "1000:1000",
            "--network=none",
            "--read-only",
            "--cap-drop=ALL",
            "--security-opt=no-new-privileges:true",
            f"--memory={memory}",
            f"--memory-swap={memory}",
            f"--cpus={cpus}",
            f"--pids-limit={pids}",
            "--tmpfs", f"/tmp:size={tmpfs_size}",
            "-v", f"{submission_dir.resolve()}:/solver:ro",
            "-e", "PYTHONUNBUFFERED=1",
            image,
        ]
        return argv, None, container_name
    raise ValueError(f"unknown sandbox mode: {mode!r}")


def _validate_submission_layout(submission_dir: Path) -> str | None:
    """Enforce the single-file solver contract at intake.

    The submission directory must contain exactly one regular file named
    ``solver.py`` — nothing else. No helper modules, no data payloads, no
    subdirectories, no symlinks. This is load-bearing: in docker mode the
    whole submission directory is bind-mounted into the container, so any
    extra file would be importable/readable at runtime and would bypass the
    ``max_solver_bytes`` cap that only measures ``solver.py`` itself.

    Returns ``None`` if the layout is valid, otherwise a human-readable
    error string describing the violation.
    """
    try:
        entries = list(submission_dir.iterdir())
    except OSError as exc:
        return f"cannot read submission directory: {exc}"

    solver = submission_dir / "solver.py"
    extras = [e.name for e in entries if e.name != "solver.py"]
    if extras:
        extras_sorted = sorted(extras)
        return (
            "submission must contain only solver.py; "
            f"found extra entries: {extras_sorted!r}"
        )
    if not solver.exists():
        return "solver.py not found"
    # Reject symlinks and non-regular files. ``is_file()`` resolves symlinks,
    # so also explicitly check ``is_symlink()`` on the link itself.
    if solver.is_symlink():
        return "solver.py must be a regular file, not a symlink"
    if not solver.is_file():
        return "solver.py must be a regular file"
    return None


def _load_prompt_template(submission_dir: Path) -> str:
    """Load prompt template for a submission.

    Solo format is single-file: the template lives as a top-level
    ``PROMPT = "..."`` string constant in ``solver.py``. AST-only extraction;
    the module is never imported. Any ``prompt.txt`` in the submission dir is
    intentionally ignored — one rule, one entry point.
    """
    solver_path = submission_dir / "solver.py"
    if solver_path.exists():
        return _extract_prompt_from_solver(solver_path)
    return ""


def _format_history(judge_log: list[dict]) -> str:
    """Format accumulated judge attempts into a readable history block."""
    if not judge_log:
        return "(no previous attempts)"

    parts = []
    for i, entry in enumerate(judge_log, 1):
        req = entry.get("request", {})
        resp = entry.get("response", {})
        verdict = req.get("verdict", "?")
        status = resp.get("status", "unknown")
        part = f"Attempt {i}: verdict={verdict}, judge={status}"
        stderr = resp.get("stderr", "")
        message = resp.get("message", "")
        err = stderr or message
        if err:
            # Keep error concise but useful
            if len(err) > 600:
                err = err[:600] + "\n... (truncated)"
            part += f"\n  Error: {err}"
        parts.append(part)
    return "\n".join(parts)


def _fill_prompt_template(
    template: str,
    problem: dict,
    solver_context: dict,
    judge_log: list[dict],
) -> str:
    """Fill prompt template with {problem.*}, {solver.*}, {history.*} placeholders."""
    import re as _re

    # {problem.*} — from problem data
    eq1_name = f"Equation{problem.get('eq1_id', '')}"
    eq2_name = f"Equation{problem.get('eq2_id', '')}"
    problem_vars = {
        "problem.id": problem.get("id", ""),
        "problem.eq1_id": str(problem.get("eq1_id", "")),
        "problem.eq2_id": str(problem.get("eq2_id", "")),
        "problem.eq1_name": eq1_name,
        "problem.eq2_name": eq2_name,
        "problem.equation1": problem.get("equation1", ""),
        "problem.equation2": problem.get("equation2", ""),
        # Backward compat aliases for prompts
        "problem.equation1_id": eq1_name,
        "problem.equation2_id": eq2_name,
    }

    # {history.*} — from accumulated judge interactions
    history_vars = {
        "history.attempts": _format_history(judge_log),
        "history.round": str(len(judge_log)),
    }
    if judge_log:
        last = judge_log[-1].get("response", {})
        history_vars["history.last_error"] = (
            last.get("stderr") or last.get("message") or ""
        )
        history_vars["history.last_status"] = last.get("status", "")
    else:
        history_vars["history.last_error"] = ""
        history_vars["history.last_status"] = ""

    # {solver.*} — from solver's context payload
    solver_vars = {f"solver.{k}": str(v) for k, v in solver_context.items()}

    # Merge all and replace
    all_vars = {**problem_vars, **history_vars, **solver_vars}
    result = template
    for key, value in all_vars.items():
        result = result.replace("{" + key + "}", value)

    # Remove any unfilled placeholders (optional: leave them or strip them)
    result = _re.sub(r"\{(problem|solver|history)\.[a-zA-Z_]+\}", "", result)

    return result


def run_solver(
    submission_dir: str | Path,
    problem: dict,
    config: dict,
    *,
    trace_hook: Callable[[dict], None] | None = None,
) -> dict:
    """
    Run a solver subprocess for one problem.

    ``trace_hook`` is an optional callable invoked with each log entry
    (``{"type": "llm" | "judge" | "error" | …, …}``) the moment it's
    produced — i.e. as soon as an LLM call returns or a Lean compile
    finishes, not batched until ``run_solver`` returns. The playground
    uses this to stream progress into the UI so a user watching a
    multi-minute problem sees each attempt as it happens instead of
    waiting for the whole run to end.

    Cancellation is out-of-band: callers wanting to abort a running
    ``run_solver`` should run it in a subprocess and SIGKILL that
    subprocess (and the process group below it). That's what the
    playground server does — ``scripts/run_job.py`` is the subprocess
    and ``os.killpg`` is the cancel mechanism.

    Returns:
        {
            "solved": bool,
            "verdict": str | None,
            "code": str | None,
            "llm_calls": int,
            "judge_calls": int,
            "log": [...]
        }
    """
    submission_dir = Path(submission_dir)
    solver_path = submission_dir / "solver.py"
    if not solver_path.exists():
        return {
            "solved": False, "verdict": None, "code": None,
            "llm_calls": 0, "judge_calls": 0,
            "log": [{"type": "error", "message": f"solver.py not found in {submission_dir}"}],
        }

    # Single-file layout check: runs before the size cap so that the bytes
    # we measure are the bytes that will actually run. See
    # ``_validate_submission_layout`` for why extras are rejected.
    layout_err = _validate_submission_layout(submission_dir)
    if layout_err is not None:
        return {
            "solved": False, "verdict": None, "code": None,
            "llm_calls": 0, "judge_calls": 0,
            "log": [{"type": "error", "message": layout_err}],
        }

    # Intake size check: refuse solvers larger than the configured cap (500 KB
    # by default). Enforced here — before we touch the file for prompt
    # extraction or launch any subprocess — so oversized submissions cost
    # essentially nothing. os.path.getsize avoids reading the file body; this
    # matters for pathologically large solver.py files on disk.
    max_solver_bytes = config.get("judge", {}).get("max_solver_bytes")
    if max_solver_bytes is not None:
        try:
            actual_bytes = os.path.getsize(solver_path)
        except OSError as e:
            return {
                "solved": False, "verdict": None, "code": None,
                "llm_calls": 0, "judge_calls": 0,
                "log": [{"type": "error", "message": f"could not stat solver.py: {e}"}],
            }
        if actual_bytes > max_solver_bytes:
            return {
                "solved": False, "verdict": None, "code": None,
                "llm_calls": 0, "judge_calls": 0,
                "log": [{
                    "type": "error",
                    "message": (
                        f"solver.py is {actual_bytes} bytes, exceeds limit "
                        f"{max_solver_bytes} bytes"
                    ),
                }],
            }

    prompt_template = _load_prompt_template(submission_dir)

    solver_config = config["solver"]
    timeout = solver_config["timeout_seconds"]
    # Single source of truth for "have we run out of time?". Every blocking
    # call (LLM HTTP, Lean compile) clamps its own timeout against this so
    # the proxy returns within ``timeout + small_epsilon`` even if a call is
    # issued just before the watchdog fires.
    deadline = time.monotonic() + timeout

    public_problem = problem
    startup_msg = {
        "problem": public_problem,
        "budget": {
            "timeout_seconds": timeout,
            "max_code_length": config["judge"]["max_code_length"],
            "max_false_cert_bytes": config["judge"]["max_false_cert_bytes"],
        },
    }

    log: list[dict] = []
    judge_log: list[dict] = []  # Accumulated judge attempts for {history.*}
    llm_calls = 0
    judge_calls = 0
    solved = False
    final_verdict = None
    final_code = None
    timed_out = False

    # Build a minimal environment for the solver — no secrets leak through.
    solver_env = {
        k: os.environ[k]
        for k in ("PATH", "HOME", "USER", "LANG", "TERM", "TMPDIR",
                   "PYTHONPATH", "PYTHONIOENCODING")
        if k in os.environ
    }
    solver_env["PYTHONIOENCODING"] = "utf-8"

    sandbox_cfg = config.get("sandbox", DEFAULT_SANDBOX_CONFIG)
    argv, cwd, container_name = _build_solver_argv(submission_dir, sandbox_cfg)
    subprocess_env = _solver_subprocess_env(sandbox_cfg, solver_env)

    def _kill_container() -> None:
        """Best-effort `docker kill` so the container does not outlive the proxy.

        The host ``docker run`` CLI is a thin client: killing it (watchdog
        or cleanup) sends SIGKILL to the CLI process but does not stop the
        container the daemon spawned. Without this, a solver that ignores
        stdin and spins hot would keep burning CPU after the proxy returns.
        """
        if not container_name:
            return
        try:
            subprocess.run(
                ["docker", "kill", container_name],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=5,
            )
        except (OSError, subprocess.TimeoutExpired):
            pass

    # stderr goes to a PIPE drained by a dedicated thread into a bounded
    # ring of strings. This keeps Python tracebacks visible (a contestant
    # solver that crashes used to exit with no diagnostic at all) while
    # avoiding the kernel-pipe-buffer deadlock that would happen if we
    # left stderr=PIPE without reading it.
    proc = subprocess.Popen(
        argv,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=cwd,
        text=True,
        env=subprocess_env,
    )

    stderr_lock = threading.Lock()
    stderr_tail: list[str] = []
    stderr_total_chars = [0]

    def _drain_stderr() -> None:
        if proc.stderr is None:
            return
        try:
            while True:
                chunk = proc.stderr.read(4096)
                if not chunk:
                    return
                with stderr_lock:
                    stderr_tail.append(chunk)
                    stderr_total_chars[0] += len(chunk)
                    # Compact when we've accumulated more than 2× the cap so
                    # we keep at most ~2× MAX in memory at any moment.
                    if stderr_total_chars[0] > MAX_STDERR_TAIL_CHARS * 2:
                        joined = "".join(stderr_tail)[-MAX_STDERR_TAIL_CHARS:]
                        stderr_tail.clear()
                        stderr_tail.append(joined)
                        stderr_total_chars[0] = len(joined)
        except (OSError, ValueError):
            return

    stderr_thread = threading.Thread(target=_drain_stderr, daemon=True)
    stderr_thread.start()

    # Timeout watchdog: SIGKILL the solver (and, for docker sandboxes, its
    # container) at the configured deadline. Polls rather than a single
    # ``time.sleep(timeout)`` so if the solver exits early we're not still
    # asleep.  Cancellation is *not* this thread's job — callers cancel by
    # SIGKILL-ing the whole process running ``run_solver``.
    watchdog_stop = threading.Event()

    def _watchdog():
        nonlocal timed_out
        deadline = time.monotonic() + timeout
        while not watchdog_stop.is_set():
            if proc.poll() is not None:
                return
            if time.monotonic() >= deadline:
                timed_out = True
                proc.kill()
                _kill_container()
                return
            time.sleep(0.1)

    watchdog = threading.Thread(target=_watchdog, daemon=True)
    watchdog.start()

    def _trace(entry: dict) -> None:
        """Append to the accumulated log and (optionally) stream out.

        Callers hold the invariant: every log entry visible in the final
        result was also offered to ``trace_hook`` at the moment it landed.
        Hook exceptions are swallowed — the proxy's correctness must not
        depend on the UI's ability to consume the stream.
        """
        log.append(entry)
        if trace_hook is not None:
            try:
                trace_hook(entry)
            except Exception:  # noqa: BLE001
                pass

    def _trace_start(entry: dict) -> None:
        """Stream a lifecycle event (``llm_start`` / ``judge_start``)
        without adding it to the persistent log.

        Without this, the UI saw no sign a call had begun until it
        finished — 30–60 s of silence for a high-reasoning LLM round.
        We don't write these to ``log`` because the completion entry
        already carries the same identifying info and a duplicate pair
        per call would bloat the result log for consumers that don't
        care about stream lifecycle.
        """
        if trace_hook is not None:
            try:
                trace_hook(entry)
            except Exception:  # noqa: BLE001
                pass

    try:
        # Send startup message
        proc.stdin.write(json.dumps(startup_msg) + "\n")
        proc.stdin.flush()

        # Main I/O loop: read lines from solver stdout with a per-line cap.
        # A hostile solver that writes a huge payload without a newline would
        # otherwise block in readline with unbounded memory growth.
        while True:
            if timed_out:
                break
            # Read one char past the cap so a line of exactly MAX_STDOUT_LINE_CHARS
            # chars + '\n' fits; anything longer is detected by length > cap.
            line = proc.stdout.readline(MAX_STDOUT_LINE_CHARS + 1)
            if not line:
                break  # EOF
            if len(line) > MAX_STDOUT_LINE_CHARS:
                _trace({
                    "type": "error",
                    "message": (
                        f"solver stdout line exceeded {MAX_STDOUT_LINE_CHARS} "
                        "chars; aborting"
                    ),
                })
                break

            line = line.strip()
            if not line:
                continue

            # Parse JSON protocol message
            try:
                msg = json.loads(line)
            except json.JSONDecodeError:
                continue  # Ignore non-JSON lines (debug output)

            if not isinstance(msg, dict) or "call" not in msg:
                continue

            call_type = msg["call"]
            t0 = time.time()
            remaining = deadline - time.monotonic()
            # Refuse to start any new blocking call with essentially no time
            # left — otherwise the proxy pays an unavoidable round-trip past
            # the deadline for a call that was doomed anyway.
            if remaining <= 1.0:
                timed_out = True
                break

            if call_type == "judge":
                judge_calls += 1
                verdict = msg.get("verdict", "")
                code = msg.get("code", "")
                _trace_start({
                    "type": "judge_start",
                    "verdict": verdict,
                    "code_length": len(code or ""),
                })
                # Clamp Lean timeout to the smaller of the config-declared
                # cap and the wall-clock remaining: if 50 s remain on a 300 s
                # config cap the judge gets 50 s; if 1000 s remain the judge
                # gets the 300 s the contestant was promised, never more.
                judge_cfg = config["judge"]
                response = _call_judge(
                    problem, verdict, code,
                    lean_timeout_seconds=min(
                        int(judge_cfg["lean_timeout_seconds"]),
                        int(remaining),
                    ),
                    max_code_length=int(judge_cfg["max_code_length"]),
                    max_false_cert_bytes=int(judge_cfg["max_false_cert_bytes"]),
                )

                if response.get("status") == "accepted":
                    solved = True
                    final_verdict = verdict
                    final_code = code

                elapsed = time.time() - t0
                entry = {
                    "type": "judge",
                    "request": {"verdict": msg.get("verdict"), "code": msg.get("code", "")},
                    "response": response,
                    "elapsed": round(elapsed, 2),
                }
                _trace(entry)
                judge_log.append(entry)

            elif call_type == "llm":
                llm_calls += 1
                solver_context = msg.get("context", {})
                filled_prompt = _fill_prompt_template(
                    prompt_template, public_problem, solver_context, judge_log,
                )
                _trace_start({
                    "type": "llm_start",
                    "prompt_length": len(filled_prompt),
                    "round": solver_context.get("round", str(llm_calls - 1)),
                })

                # Stream each generated delta (``reasoning`` or ``content``)
                # to the trace hook so the UI can render the model's tokens
                # as they arrive — otherwise a multi-minute high-reasoning
                # call looks identical to a hang.
                def _llm_chunk(kind: str, text: str, _round: str = solver_context.get("round", str(llm_calls - 1))) -> None:
                    _trace_start({
                        "type": "llm_chunk",
                        "round": _round,
                        "kind": kind,   # "reasoning" | "content"
                        "text": text,
                    })

                # A solver may pick any model on the evaluation allowlist
                # (``llm.models``); omitting the field keeps the default.
                # An unpinned model is refused rather than silently served —
                # reproducibility depends on the pin.
                try:
                    response = _call_llm(
                        filled_prompt, config, max_seconds=remaining,
                        stream_chunk_hook=_llm_chunk if trace_hook is not None else None,
                        model=msg.get("model"),
                    )
                except UnknownModelError as exc:
                    allowed = [
                        e.get("model")
                        for e in (config["llm"].get("models") or [])
                        if isinstance(e, dict)
                    ] or [config["llm"]["model"]]
                    response = {
                        "error": f"model {exc.args[0]!r} is not on the evaluation allowlist",
                        "allowed_models": allowed,
                    }

                elapsed = time.time() - t0
                _trace({
                    "type": "llm",
                    "request": {
                        "solver_context": msg.get("context", {}),
                        "filled_prompt": filled_prompt,
                    },
                    "response": response,
                    "elapsed": round(elapsed, 2),
                })

            else:
                response = {"error": f"unknown call type: {call_type}"}
                _trace({"type": "unknown", "request": msg, "response": response})

            # Send response back to solver
            try:
                proc.stdin.write(json.dumps(response) + "\n")
                proc.stdin.flush()
            except (BrokenPipeError, OSError):
                break

            if solved:
                break

    except Exception as e:
        _trace({"type": "error", "message": str(e)})

    finally:
        # Tell the watchdog to stop polling now that we're tearing down;
        # otherwise it would spin for another ~100 ms before noticing
        # ``proc.poll() is not None``. Harmless but noisy in logs/CPU.
        watchdog_stop.set()
        if proc.poll() is None:
            proc.terminate()
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
        # Belt-and-suspenders: the docker CLI is a client to the daemon, so
        # killing the client doesn't always stop the container (the watchdog
        # and `--rm` cover some cases, but not all: normal loop exit, broken
        # pipe, solved-early break). A final `docker kill` here guarantees no
        # container outlives the proxy regardless of exit path.
        _kill_container()

        # Drain remaining stderr now that the solver process is gone, then
        # emit a single trace entry with the tail. This is what makes a
        # crashed-solver Python traceback visible to the harness/UI — before
        # this, contestant crashes exited with no diagnostic at all.
        if proc.stderr is not None:
            try:
                proc.stderr.close()
            except Exception:  # noqa: BLE001
                pass
        stderr_thread.join(timeout=2)
        with stderr_lock:
            tail_text = "".join(stderr_tail)[-MAX_STDERR_TAIL_CHARS:]
        if tail_text and tail_text.strip():
            _trace({
                "type": "solver_stderr",
                "tail": tail_text,
                "returncode": proc.returncode,
            })

    if timed_out and not solved:
        _trace({"type": "timeout", "message": f"solver exceeded {timeout}s timeout"})

    return {
        "solved": solved,
        "verdict": final_verdict,
        "code": final_code,
        "llm_calls": llm_calls,
        "judge_calls": judge_calls,
        "log": log,
    }
