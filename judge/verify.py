from __future__ import annotations

import hashlib
import json
import os
import re
import secrets
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
JUDGE_DIR = Path(__file__).resolve().parent
DEFAULT_LEAN = Path(os.environ.get("LEAN_BIN", "lean"))
DEFAULT_LAKE = Path(os.environ.get("LAKE_BIN", "lake"))
DEFAULT_ARTIFACT_DIR = REPO_ROOT / ".artifacts"
ANSWER_KEYS = {"verdict", "code"}
PROBLEM_KEYS = {"id", "eq1_id", "eq2_id", "equation1", "equation2"}
PROBLEM_OPTIONAL_KEYS = {"proof_policy", "answer", "index", "difficulty"}
BANNED_PROOF_TOKENS = (
    # Proof-level holes
    "sorry", "admit", "sorryAx", "mkSorry",
    # Tracing / debug-write to stdout
    "dbg_trace", "dbgTrace",
    # Metaprogram execution at elaboration time (arbitrary IO).
    # ``run_cmd`` / ``run_elab`` are the same capability as ``run_tac`` at
    # command level; ``@[init f]`` registers a module initializer that runs when
    # Problem.lean does ``import Submission`` — i.e. before the judge's own
    # commands — which is enough to forge the dependency report and exit.
    "run_tac", "run_cmd", "run_elab", "initialize", "builtin_initialize", "@[init",
    # Elab-time command execution (#eval) and custom elaborators/macros
    "#eval", "#exit", "#reduce", "#synth", "#check_eval",
    "elab", "elab_rules", "macro", "macro_rules", "syntax",
    # Parser extensions. These are persistent and travel through the .olean, and
    # Problem.lean is PARSED after ``import Submission`` — so a submission that
    # declares ``notation "Goal" => True`` changes what the judge's own
    # ``theorem _judge_checked_<nonce> : Goal := submission`` means.
    "notation", "notation3", "infix", "infixl", "infixr", "prefix", "postfix",
    # Unsafe declarations (can bypass type-checking)
    "unsafe", "implemented_by", "extern",
    # Kernel type-checking must not be skipped for the submitted declaration.
    "skipKernelTC",
    # Unsafe casts / IO primitives (bypass Lean's kernel guarantees)
    "unsafeCast", "unsafeIO", "unsafePerformIO",
)
EQUATION_NAME_RE = re.compile(r"^Equation[0-9]+$")
# These defaults mirror the reference values in ``pipeline/config.json``
# (``judge.max_code_length`` / ``judge.max_false_cert_bytes`` /
# ``judge.lean_timeout_seconds``). Both evaluation tracks propagate the
# config values explicitly (Solo via ``pipeline.proxy._call_judge``,
# Marathon via ``pipeline.marathon_score``); the constants here exist so a
# bare ``verify_answer(...)`` call enforces the same documented contract.
MAX_CODE_LENGTH = 100_000
MAX_FALSE_CERT_BYTES = 20_000
LEAN_TIMEOUT_SECONDS = 300
MANIFEST_WARNING_SUBSTRING = "manifest out of date: git revision of dependency 'mathlib' changed"
# Lean 4.32 added the default-on ``linter.defProp``, which fires on every
# ``def <name> : <Prop>``. The judge's own documented submission shape is
# ``def submission : Goal := …`` with ``Goal : Prop``, so the linter tells every
# contestant to rewrite the exact shape this judge requires. It is suppressed at
# the invocation rather than filtered out of the output, so that genuine linter
# diagnostics a contestant may rely on (Mathlib's ``linter.unnecessarySimpa``
# and friends) still reach them intact.
LEAN_LINTER_FLAGS = ("-D", "linter.defProp=false")
REPORT_PREFIX = "JUDGE_REPORT "


class JudgeInfrastructureError(RuntimeError):
    """Raised when local tooling or organizer-owned inputs are broken."""


class JudgeConfigurationError(RuntimeError):
    """Raised when organizer-provided problem configuration is invalid."""


class DuplicateJsonKeyError(ValueError):
    """Raised when a raw JSON payload repeats an object key."""


@dataclass(frozen=True)
class ProofPolicy:
    """Axiom and declaration allowlists for proof validation.

    When allowed_axioms is set, every axiom used by the proof must appear
    in the tuple.  When allowed_declarations / allowed_declaration_prefixes
    are not None, every direct declaration must be explicitly allowed.
    """
    allowed_axioms: tuple[str, ...] = ()
    # None means "no declaration check" (default when problem has no policy).
    allowed_declarations: tuple[str, ...] | None = None
    allowed_declaration_prefixes: tuple[str, ...] | None = None


@dataclass(frozen=True)
class ProblemSpec:
    problem_id: str
    eq1_id: int
    eq2_id: int
    equation1: str
    equation2: str
    proof_policy: ProofPolicy

    @property
    def eq1_name(self) -> str:
        return f"Equation{self.eq1_id}"

    @property
    def eq2_name(self) -> str:
        return f"Equation{self.eq2_id}"


@dataclass(frozen=True)
class AnswerSpec:
    verdict: str
    code: str


@dataclass(frozen=True)
class JudgeConfig:
    lean_bin: Path = DEFAULT_LEAN
    lake_bin: Path = DEFAULT_LAKE
    artifact_dir: Path = DEFAULT_ARTIFACT_DIR
    lean_timeout_seconds: int = LEAN_TIMEOUT_SECONDS
    max_code_length: int = MAX_CODE_LENGTH
    max_false_cert_bytes: int = MAX_FALSE_CERT_BYTES


def _result(
    status: str,
    error_code: str,
    message: str,
    *,
    verdict: str | None = None,
    artifact_path: str | None = None,
    direct_declarations: list[str] | None = None,
    axioms: list[str] | None = None,
    stdout: str = "",
    stderr: str = "",
) -> dict[str, Any]:
    return {
        "status": status,
        "error_code": error_code,
        "message": message,
        "verdict": verdict,
        "artifact_path": artifact_path,
        "direct_declarations": direct_declarations or [],
        "axioms": axioms or [],
        "stdout": stdout,
        "stderr": stderr,
    }


def _normalize_output(text: str) -> str:
    kept: list[str] = []
    for line in text.splitlines():
        if MANIFEST_WARNING_SUBSTRING in line:
            continue
        if line.startswith(REPORT_PREFIX):
            continue
        if line.strip():
            kept.append(line.rstrip())
    return "\n".join(kept)


def _strip_paths(text: str, *, art_dir: Path | None = None) -> str:
    """Replace judge-internal absolute paths with stable placeholders.

    Lean error messages include absolute file paths like
    ``/Users/you/.../.artifacts/<id>/Submission.lean:3:12`` that leak the
    organizer's working directory and artifact hashing. Contestants should see
    ``Submission.lean:3:12`` instead.
    """
    if not text:
        return text
    if art_dir is not None:
        text = text.replace(str(art_dir) + os.sep, "")
        text = text.replace(str(art_dir), "")
    text = text.replace(str(REPO_ROOT) + os.sep, "")
    text = text.replace(str(REPO_ROOT), "")
    return text


def _resolve_config(config: JudgeConfig | None) -> JudgeConfig:
    if config is not None:
        resolved = config
    else:
        resolved = JudgeConfig(
            lean_bin=Path(os.environ.get("LEAN_BIN", str(DEFAULT_LEAN))).expanduser(),
            lake_bin=Path(os.environ.get("LAKE_BIN", str(DEFAULT_LAKE))).expanduser(),
            artifact_dir=Path(os.environ.get("JUDGE_ARTIFACT_DIR", str(DEFAULT_ARTIFACT_DIR))).expanduser(),
            lean_timeout_seconds=int(os.environ.get("LEAN_TIMEOUT_SECONDS", str(LEAN_TIMEOUT_SECONDS))),
            max_code_length=int(os.environ.get("MAX_CODE_LENGTH", str(MAX_CODE_LENGTH))),
            max_false_cert_bytes=int(os.environ.get("MAX_FALSE_CERT_BYTES", str(MAX_FALSE_CERT_BYTES))),
        )

    if not resolved.lean_bin.exists() and not shutil.which(str(resolved.lean_bin)):
        raise JudgeInfrastructureError(f"missing lean binary: {resolved.lean_bin}")
    if not resolved.lake_bin.exists() and not shutil.which(str(resolved.lake_bin)):
        raise JudgeInfrastructureError(f"missing lake binary: {resolved.lake_bin}")

    resolved.artifact_dir.mkdir(parents=True, exist_ok=True)
    return resolved


_LAKE_LEAN_PATH_CACHE: dict[Path, str] = {}


def _static_lake_lean_path() -> str | None:
    """Compute LEAN_PATH by globbing .lake/packages/*/.lake/build/lib/lean + .lake/build/lib/lean.

    Returns None if no .lake dir exists. Doesn't invoke lake — safe on a ro mount.
    """
    lake_dir = REPO_ROOT / ".lake"
    if not lake_dir.is_dir():
        return None
    paths: list[str] = []
    pkgs = lake_dir / "packages"
    if pkgs.is_dir():
        for child in sorted(pkgs.iterdir()):
            libdir = child / ".lake" / "build" / "lib" / "lean"
            if libdir.is_dir():
                paths.append(str(libdir))
    own_build = lake_dir / "build" / "lib" / "lean"
    if own_build.is_dir():
        paths.append(str(own_build))
    if not paths:
        return None
    return os.pathsep.join(paths)


def _get_lake_lean_path(config: JudgeConfig) -> str:
    """Return LEAN_PATH covering mathlib + judge build dirs.

    Preference order:
      1. JUDGE_LEAN_PATH env (operator override)
      2. `lake env` — authoritative but requires a writable .lake
      3. Static glob of .lake/packages/*/.lake/build/lib/lean — works on read-only mount
    """
    key = config.lake_bin.resolve() if config.lake_bin.exists() else Path(str(config.lake_bin))
    cached = _LAKE_LEAN_PATH_CACHE.get(key)
    if cached is not None:
        return cached

    override = os.environ.get("JUDGE_LEAN_PATH")
    if override:
        _LAKE_LEAN_PATH_CACHE[key] = override
        return override

    # Try `lake env` first — it's authoritative, includes system paths.
    try:
        proc = subprocess.run(
            [str(config.lake_bin), "env", "bash", "-c", "echo $LEAN_PATH"],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            timeout=30,
        )
        if proc.returncode == 0 and proc.stdout.strip():
            lean_path = proc.stdout.strip()
            _LAKE_LEAN_PATH_CACHE[key] = lean_path
            return lean_path
    except FileNotFoundError:
        pass

    # Fall back to static globbing (works on ro mount)
    static = _static_lake_lean_path()
    if static is None:
        raise JudgeInfrastructureError(
            "no LEAN_PATH available: lake env failed and no .lake/ directory found"
        )
    _LAKE_LEAN_PATH_CACHE[key] = static
    return static


def _write_problem_module(
    problem: "ProblemSpec",
    verdict: str,
    art_dir: Path,
    config: JudgeConfig,
) -> None:
    """Write and compile art_dir/JudgeProblem.olean with equation defs + Goal abbrev.

    JudgeProblem is the judge-controlled module imported by Submission.
    It binds:
      * ``EquationLHS`` / ``EquationRHS`` — the two problem equations
      * ``Goal``                         — an ``abbrev`` naming the target
                                           type for *this* verdict

    The module is top-level (not under JudgeMagma.*) so art_dir on LEAN_PATH
    does not create a partial-namespace conflict with the pre-compiled
    JudgeMagma modules in JUDGE_DIR.  Submissions only need
    ``import JudgeProblem`` — they do not have to restate the goal shape.
    """
    # Concrete universe ``Type`` (= ``Type 0``) in both branches.  Using
    # ``Type _`` here would leave a metavariable that Lean can't resolve at
    # ``abbrev`` elaboration (no term to unify against, unlike the old
    # ``theorem submission : <goal> := <proof>`` shape), producing
    # ``Failed to infer universe levels in binder type Magma.{?u} G``.
    # Submitters work with concrete carriers (``Fin n``, ``Nat``,
    # submission-defined inductives — finite and infinite alike) which
    # all live in ``Type 0``, so restricting ``Goal`` to ``Type 0`` is
    # not a practical loss.
    if verdict == "true":
        goal = "∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G"
    else:
        goal = "∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G"

    source = art_dir / "JudgeProblem.lean"
    olean = art_dir / "JudgeProblem.olean"

    source.write_text(
        "import JudgeMagma.Magma\n"
        "\n"
        f"{_equation_def('EquationLHS', problem.equation1)}\n"
        f"{_equation_def('EquationRHS', problem.equation2)}\n"
        "\n"
        "-- Target type for this verify (verdict-specific, judge-controlled).\n"
        f"abbrev Goal : Prop := {goal}\n",
        encoding="utf-8",
    )

    env = _make_lean_env(config, [str(art_dir)])
    proc = subprocess.run(
        [str(config.lean_bin), f"--root={art_dir}", "-o", str(olean), str(source)],
        cwd=art_dir,
        env=env,
        text=True,
        capture_output=True,
    )
    if proc.returncode != 0:
        details = _normalize_output(proc.stderr) or _normalize_output(proc.stdout) or "unknown Lean failure"
        raise JudgeInfrastructureError(f"failed to compile JudgeProblem: {details}")


def _parse_string_list(raw: Any, field_name: str) -> tuple[str, ...]:
    if not isinstance(raw, list):
        raise JudgeConfigurationError(f"problem.{field_name} must be a JSON array")
    values: list[str] = []
    for value in raw:
        if not isinstance(value, str) or not value:
            raise JudgeConfigurationError(f"problem.{field_name} entries must be non-empty strings")
        values.append(value)
    return tuple(values)


def _parse_proof_policy(raw: Any) -> ProofPolicy:
    """Parse proof_policy from problem JSON.

    When the field is absent (None), return the default policy: no axioms
    allowed, no declaration check.  When present, parse all three sub-fields.
    Sub-fields that are absent default to None (no check), not empty (nothing allowed).
    """
    if raw is None:
        return ProofPolicy()

    if not isinstance(raw, dict):
        raise JudgeConfigurationError("proof_policy must be a JSON object")

    allowed_keys = {"allowed_axioms", "allowed_declarations", "allowed_declaration_prefixes"}
    extra = set(raw) - allowed_keys
    if extra:
        raise JudgeConfigurationError(f"proof_policy contains unexpected keys: {', '.join(sorted(extra))}")

    allowed_axioms = _parse_string_list(raw.get("allowed_axioms", []), "proof_policy.allowed_axioms")
    # Missing declaration fields → None (no check), not () (empty allowlist)
    allowed_declarations: tuple[str, ...] | None = None
    if "allowed_declarations" in raw:
        allowed_declarations = _parse_string_list(
            raw["allowed_declarations"], "proof_policy.allowed_declarations"
        )
    allowed_declaration_prefixes: tuple[str, ...] | None = None
    if "allowed_declaration_prefixes" in raw:
        allowed_declaration_prefixes = _parse_string_list(
            raw["allowed_declaration_prefixes"], "proof_policy.allowed_declaration_prefixes"
        )
    return ProofPolicy(
        allowed_axioms=allowed_axioms,
        allowed_declarations=allowed_declarations,
        allowed_declaration_prefixes=allowed_declaration_prefixes,
    )


def _normalize_equation_text(text: str) -> str:
    """Normalize equation text: replace every '*' with '◇'.

    The equation DSL has no arithmetic '*' — every '*' is the magma operator.
    Upstream data may use '*' (HuggingFace) or '◇' (Lean-native) or mix both;
    Lean requires '◇', so the judge normalizes unconditionally.
    """
    return text.replace("*", "◇")


def _parse_problem(problem: Any) -> ProblemSpec:
    if not isinstance(problem, dict):
        raise JudgeConfigurationError("problem must be a JSON object")

    keys = set(problem)
    allowed_keys = PROBLEM_KEYS | PROBLEM_OPTIONAL_KEYS
    if keys - allowed_keys:
        extras = ", ".join(sorted(keys - allowed_keys))
        raise JudgeConfigurationError(f"problem contains unexpected keys: {extras}")
    if not PROBLEM_KEYS.issubset(keys):
        missing = ", ".join(sorted(PROBLEM_KEYS - keys))
        raise JudgeConfigurationError(f"problem is missing required keys: {missing}")

    pid = problem["id"]
    if not isinstance(pid, str) or not pid.strip():
        raise JudgeConfigurationError("problem.id must be a non-empty string")

    for field in ("eq1_id", "eq2_id"):
        value = problem[field]
        if not isinstance(value, int) or value < 0:
            raise JudgeConfigurationError(f"problem.{field} must be a non-negative integer")

    for field in ("equation1", "equation2"):
        value = problem[field]
        if not isinstance(value, str) or not value.strip():
            raise JudgeConfigurationError(f"problem.{field} must be a non-empty string")

    proof_policy = _parse_proof_policy(problem.get("proof_policy"))
    return ProblemSpec(
        problem_id=problem["id"],
        eq1_id=problem["eq1_id"],
        eq2_id=problem["eq2_id"],
        equation1=_normalize_equation_text(problem["equation1"]),
        equation2=_normalize_equation_text(problem["equation2"]),
        proof_policy=proof_policy,
    )


def _reject_duplicate_keys(pairs: list[tuple[Any, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    seen: set[str] = set()
    for key, value in pairs:
        if not isinstance(key, str):
            raise DuplicateJsonKeyError("non-string JSON object key")
        if key in seen:
            raise DuplicateJsonKeyError(key)
        seen.add(key)
        result[key] = value
    return result


def _parse_answer_payload(
    raw_answer: str,
    *,
    max_code_length: int = MAX_CODE_LENGTH,
) -> tuple[AnswerSpec | None, dict[str, Any]]:
    try:
        parsed = json.loads(raw_answer, object_pairs_hook=_reject_duplicate_keys)
    except DuplicateJsonKeyError as exc:
        return None, _result(
            "malformed",
            "DUPLICATE_JSON_KEYS",
            f"raw answer contains duplicate JSON key: {exc}",
        )
    except json.JSONDecodeError as exc:
        return None, _result("unparsed", "UNPARSED_JSON", f"raw answer is not valid JSON: {exc.msg}")

    if not isinstance(parsed, dict):
        return None, _result("malformed", "ANSWER_NOT_OBJECT", "answer must be a JSON object")
    if set(parsed) != ANSWER_KEYS:
        return None, _result(
            "malformed",
            "ANSWER_SCHEMA_ERROR",
            "answer must contain exactly {'verdict', 'code'}",
            verdict=parsed.get("verdict") if isinstance(parsed.get("verdict"), str) else None,
        )

    verdict = parsed.get("verdict")
    code = parsed.get("code")
    if verdict not in {"true", "false"}:
        return None, _result("malformed", "INVALID_VERDICT", "verdict must be exactly 'true' or 'false'")
    if not isinstance(code, str) or not code.strip():
        return None, _result(
            "malformed",
            "INVALID_CODE_FIELD",
            "code must be a non-empty string",
            verdict=verdict,
        )
    # ``json.loads`` accepts lone-surrogate escapes (e.g. "\ud83d") and yields a
    # Python str that cannot be UTF-8 encoded. Every downstream step — the byte
    # cap here, the false-cert byte cap, and writing Submission.lean — encodes
    # to UTF-8, so an unguarded ``.encode`` raises UnicodeEncodeError and the
    # answer escapes the five-status contract (in Marathon it aborts the whole
    # batch). Such code is not valid Lean source text: reject it as malformed.
    try:
        code_bytes_len = len(code.encode("utf-8"))
    except UnicodeEncodeError:
        return None, _result(
            "malformed",
            "CODE_NOT_UTF8",
            "code is not encodable as UTF-8 (contains unpaired surrogates)",
            verdict=verdict,
        )
    if code_bytes_len > max_code_length:
        return None, _result(
            "malformed",
            "CODE_TOO_LONG",
            f"code must have UTF-8 length <= {max_code_length} bytes",
            verdict=verdict,
        )

    return AnswerSpec(verdict=verdict, code=code), {}


def _find_banned_token(code: str) -> str | None:
    """Scan for banned identifiers / commands.

    Lexer rules:
      - Tokens starting with `#` or `@`, or containing a trailing space, are
        matched as a non-word-boundary literal (Lean commands like `#eval`,
        `elab `, and attribute forms like `@[init`).
      - Identifier tokens use word boundaries so `sorry` matches `sorry` but not
        `sorryFreeProof`.
    """
    for token in BANNED_PROOF_TOKENS:
        if token.startswith(("#", "@")) or token.endswith(" "):
            # Literal substring scan for Lean commands that aren't word-bounded
            if re.search(re.escape(token), code):
                return token
        else:
            if re.search(rf"\b{re.escape(token)}\b", code):
                return token
    return None


_EQUATION_TEXT_RE = re.compile(r"^[\sa-zA-Z0-9◇=()]+$")


def _equation_def(name: str, text: str) -> str:
    """Build an inline equation definition from name and text.

    text is like "x = y ◇ x" or "x ◇ y = y ◇ ((y ◇ x) ◇ y)".
    Variables are single lowercase letters (x, y, z, w, etc.).

    The equation text is interpolated verbatim into Lean source, so it must
    be tightly constrained to prevent organizer-side injection via malformed
    problem data: only ASCII letters/digits, whitespace, the ``◇`` operator,
    ``=``, and balanced parentheses are allowed.
    """
    if not isinstance(name, str) or not re.fullmatch(r"[A-Za-z][A-Za-z0-9]*", name):
        raise JudgeConfigurationError(f"invalid equation def name: {name!r}")
    if not isinstance(text, str) or not _EQUATION_TEXT_RE.fullmatch(text):
        raise JudgeConfigurationError(
            f"equation text contains disallowed characters: {text!r}"
        )
    depth = 0
    for ch in text:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth < 0:
                raise JudgeConfigurationError(
                    f"unbalanced parentheses in equation text: {text!r}"
                )
    if depth != 0:
        raise JudgeConfigurationError(
            f"unbalanced parentheses in equation text: {text!r}"
        )

    # Preserve order of first appearance in the equation text
    seen = set()
    variables = []
    for v in re.findall(r'\b([a-z])\b', text):
        if v not in seen:
            seen.add(v)
            variables.append(v)
    binders = " ".join(f"({v} : G)" for v in variables)
    return f"@[reducible] def {name} (G : Type _) [Magma G] : Prop := ∀ {binders}, {text}"


def _render_problem_source(nonce: str) -> str:
    """Generate Problem.lean — the judge-controlled project root.

    Problem.lean asserts ``theorem _judge_checked_<nonce> : Goal := submission``,
    where ``Goal`` is the verdict-specific abbrev from ``JudgeProblem`` and
    ``submission`` is the term exposed by the submitter's ``Submission.lean``.
    The dependency policy is reported on that named binding as well as on
    ``submission`` — see the comment in the body for why both are required.

    Splitting the theorem statement into a separate (judge-controlled) file
    is what lets the submitter stay out of type-header bookkeeping: any
    ``def submission : Goal := …`` (or a term whose type is definitionally
    equal to ``Goal``) will type-check.
    """
    # The checked binding MUST be named, and the policy MUST be computed on it
    # — not on ``submission`` alone.
    #
    # A polymorphic submission such as
    #     class Cheat (P : Prop) where val : P
    #     axiom cheatAx : Goal
    #     instance : Cheat Goal := ⟨cheatAx⟩
    #     def submission {P : Prop} [inst : Cheat P] : P := inst.val
    # has an EMPTY axiom closure of its own: ``submission`` never mentions
    # ``cheatAx``. The axiom only enters when instance resolution instantiates
    # ``submission`` at this use site. Reporting on ``submission`` alone (the
    # anonymous-``example`` shape this file used before) therefore laundered any
    # axiom — including the ones ``native_decide`` adds — past every policy
    # check, for either verdict and independently of the problem.
    #
    # Reporting on the named binding closes that: ``collectAxioms`` on it walks
    # the instantiated term. Both reports are emitted and unioned, because the
    # direct-declaration set of the submission root is still the informative one
    # for the declaration allowlist. The nonce is part of the name so a
    # submission cannot pre-declare it and shadow the check.
    checked = f"_judge_checked_{nonce}"
    return (
        "import JudgeSupport.Inspect\n"
        "import JudgeProblem\n"
        "import Submission\n"
        "\n"
        f"theorem {checked} : Goal := submission\n"
        "\n"
        f'#judge_report submission "{nonce}"\n'
        f'#judge_report {checked} "{nonce}"\n'
    )


def _artifact_dir(artifact_root: Path, problem: ProblemSpec, raw_answer: str) -> Path:
    digest = hashlib.sha256(raw_answer.encode("utf-8")).hexdigest()[:12]
    return artifact_root / f"{problem.problem_id}.{digest}"


def _parse_report(stdout: str, nonce: str) -> dict[str, Any]:
    """Merge every nonce-matching dependency report into one policy input.

    ``_render_problem_source`` emits two reports: one for ``submission`` and one
    for the named binding that is actually kernel-checked. The policy is applied
    to the UNION, so an axiom that only enters through instance resolution at
    the use site cannot be laundered by reporting on the uninstantiated
    ``submission`` alone.
    """
    matches: list[dict[str, Any]] = []
    for line in stdout.splitlines():
        if line.startswith(REPORT_PREFIX):
            try:
                data = json.loads(line[len(REPORT_PREFIX) :])
            except json.JSONDecodeError:
                continue
            # ``data`` may be any JSON value (null, list, string, number, bool);
            # skip non-dict payloads rather than crash with AttributeError.
            if isinstance(data, dict) and data.get("nonce") == nonce:
                matches.append(data)
    if not matches:
        raise JudgeInfrastructureError("Lean finished without emitting a valid judge dependency report")

    # Both judge-emitted reports must be present. A submission that manages to
    # run code at import time can print a forged report and terminate the
    # process before the genuine ones are emitted; requiring both targets means
    # suppression is detected instead of silently trusted. (The union below
    # already makes *adding* a forged report useless — it can only widen the
    # dependency set, never shrink it.)
    targets = {m.get("target") for m in matches if isinstance(m.get("target"), str)}
    expected_targets = {"submission", f"_judge_checked_{nonce}"}
    if not expected_targets.issubset(targets):
        missing = ", ".join(sorted(expected_targets - targets))
        raise JudgeInfrastructureError(
            f"judge dependency report incomplete — missing report for: {missing}"
        )

    def _union(field: str) -> list[str]:
        seen: set[str] = set()
        for match in matches:
            values = match.get(field)
            if isinstance(values, list):
                seen.update(v for v in values if isinstance(v, str))
        return sorted(seen)

    merged = dict(matches[-1])
    merged["axioms"] = _union("axioms")
    merged["direct_declarations"] = _union("direct_declarations")
    return merged


def _decl_matches_prefix(name: str, prefixes: tuple[str, ...]) -> bool:
    """Check whether *name* is allowed by any prefix rule.

    A prefix that ends with ``'.'`` (e.g. ``"Eq."``) matches:
      - the namespace root itself (``"Eq"``)
      - any dotted child  (``"Eq.refl"``, ``"Eq.symm"``, …)

    A prefix without a trailing dot (e.g. ``"inst"``) is a plain
    ``startswith`` check (matches ``"instDecidableEqFin"`` etc.).
    """
    for prefix in prefixes:
        if prefix.endswith("."):
            if name == prefix[:-1] or name.startswith(prefix):
                return True
        else:
            if name.startswith(prefix):
                return True
    return False


def _policy_violations(report: dict[str, Any], policy: ProofPolicy) -> tuple[list[str], list[str]]:
    """Return (bad_axioms, bad_declarations) violating the policy."""
    allowed_axiom_set = set(policy.allowed_axioms)
    bad_axioms = [a for a in report.get("axioms", []) if a not in allowed_axiom_set]

    bad_decls: list[str] = []
    if policy.allowed_declarations is not None:
        exact_set = set(policy.allowed_declarations)
        prefixes = policy.allowed_declaration_prefixes or ()
        for decl in report.get("direct_declarations", []):
            if decl in exact_set:
                continue
            if EQUATION_NAME_RE.fullmatch(decl):
                continue
            if _decl_matches_prefix(decl, prefixes):
                continue
            bad_decls.append(decl)

    return bad_axioms, bad_decls


def _make_lean_env(config: JudgeConfig, extra_lean_paths: list[str]) -> dict[str, str]:
    """LEAN_PATH = caller-supplied entries + lake's LEAN_PATH (mathlib + deps + judge build)."""
    env = os.environ.copy()
    lean_path_entries = list(extra_lean_paths)
    lean_path_entries.append(_get_lake_lean_path(config))
    env["LEAN_PATH"] = os.pathsep.join(lean_path_entries)
    return env


def verify_answer(problem: Any, raw_answer: str, config: JudgeConfig | None = None) -> dict[str, Any]:
    # Resolve size caps before infra check: a malformed/oversized payload must
    # produce the documented `unparsed`/`malformed` status even if Lean tooling
    # happens to be missing on this machine.
    caps_cfg = config if config is not None else JudgeConfig(
        lean_timeout_seconds=int(os.environ.get("LEAN_TIMEOUT_SECONDS", str(LEAN_TIMEOUT_SECONDS))),
        max_code_length=int(os.environ.get("MAX_CODE_LENGTH", str(MAX_CODE_LENGTH))),
        max_false_cert_bytes=int(os.environ.get("MAX_FALSE_CERT_BYTES", str(MAX_FALSE_CERT_BYTES))),
    )
    problem_spec = _parse_problem(problem)
    answer_spec, early_result = _parse_answer_payload(
        raw_answer, max_code_length=caps_cfg.max_code_length
    )
    if answer_spec is None:
        return early_result

    banned = _find_banned_token(answer_spec.code)
    if banned is not None:
        return _result(
            "incomplete_proof",
            "BANNED_PLACEHOLDER",
            f"code contains banned placeholder token: {banned}",
            verdict=answer_spec.verdict,
        )

    if (
        answer_spec.verdict == "false"
        and len(answer_spec.code.encode("utf-8")) > caps_cfg.max_false_cert_bytes
    ):
        return _result(
            "malformed",
            "FALSE_CERT_TOO_LARGE",
            f"false certificate code exceeds {caps_cfg.max_false_cert_bytes} bytes",
            verdict=answer_spec.verdict,
        )

    resolved_config = _resolve_config(config)

    art_dir = _artifact_dir(resolved_config.artifact_dir, problem_spec, raw_answer)
    art_dir.mkdir(parents=True, exist_ok=True)

    # Judge writes per-verify JudgeProblem module (equation defs + Goal abbrev).
    # Submission imports this module; submission Lean is compiled verbatim.
    _write_problem_module(problem_spec, answer_spec.verdict, art_dir, resolved_config)

    submission_path = art_dir / "Submission.lean"
    submission_path.write_text(answer_spec.code, encoding="utf-8")

    # Compile Submission.lean → Submission.olean
    submission_olean = art_dir / "Submission.olean"
    env_compile = _make_lean_env(resolved_config, [str(art_dir)])
    try:
        proc_compile = subprocess.run(
            [
                str(resolved_config.lean_bin),
                f"--root={art_dir}",
                *LEAN_LINTER_FLAGS,
                "-o", str(submission_olean),
                str(submission_path),
            ],
            env=env_compile,
            text=True,
            capture_output=True,
            timeout=resolved_config.lean_timeout_seconds,
        )
    except subprocess.TimeoutExpired:
        return _result(
            "incorrect",
            "LEAN_TIMEOUT",
            "Lean compilation of submission timed out",
            verdict=answer_spec.verdict,
            artifact_path=str(art_dir),
        )

    if proc_compile.returncode != 0:
        clean_stderr = _strip_paths(_normalize_output(proc_compile.stderr), art_dir=art_dir)
        clean_stdout = _strip_paths(_normalize_output(proc_compile.stdout), art_dir=art_dir)
        message = clean_stderr or clean_stdout or "submission code failed to compile"
        return _result(
            "incorrect",
            "LEAN_REJECTED",
            message,
            verdict=answer_spec.verdict,
            artifact_path=str(art_dir),
            stdout=clean_stdout,
            stderr=clean_stderr,
        )

    # Generate and write Problem.lean (the judge-controlled project root —
    # ``theorem problem : Goal := submission`` and the dep-report directive).
    nonce = secrets.token_hex(16)
    problem_source = _render_problem_source(nonce)
    problem_path = art_dir / "Problem.lean"
    problem_path.write_text(problem_source, encoding="utf-8")

    # Run Problem.lean (with artifact dir in LEAN_PATH for import Submission)
    env_verify = _make_lean_env(resolved_config, [str(art_dir)])
    try:
        proc = subprocess.run(
            [str(resolved_config.lean_bin), f"--root={art_dir}", *LEAN_LINTER_FLAGS, str(problem_path)],
            env=env_verify,
            text=True,
            capture_output=True,
            timeout=resolved_config.lean_timeout_seconds,
        )
    except subprocess.TimeoutExpired:
        return _result(
            "incorrect",
            "LEAN_TIMEOUT",
            "Lean verification timed out",
            verdict=answer_spec.verdict,
            artifact_path=str(art_dir),
        )

    clean_stdout = _strip_paths(_normalize_output(proc.stdout), art_dir=art_dir)
    clean_stderr = _strip_paths(_normalize_output(proc.stderr), art_dir=art_dir)
    if proc.returncode != 0:
        message = clean_stderr or clean_stdout or "verification failed — submission type does not match"
        return _result(
            "incorrect",
            "LEAN_REJECTED",
            message,
            verdict=answer_spec.verdict,
            artifact_path=str(art_dir),
            stdout=clean_stdout,
            stderr=clean_stderr,
        )

    report = _parse_report(proc.stdout, nonce)
    used_axioms = sorted(str(name) for name in report.get("axioms", []))
    direct_declarations = sorted(str(name) for name in report.get("direct_declarations", []))

    bad_axioms, bad_decls = _policy_violations(report, problem_spec.proof_policy)
    if bad_axioms:
        return _result(
            "incomplete_proof",
            "DISALLOWED_AXIOMS",
            f"proof uses disallowed axioms: {', '.join(bad_axioms)}",
            verdict=answer_spec.verdict,
            artifact_path=str(art_dir),
            direct_declarations=direct_declarations,
            axioms=used_axioms,
            stdout=clean_stdout,
            stderr=clean_stderr,
        )
    if bad_decls:
        return _result(
            "incomplete_proof",
            "DISALLOWED_DECLARATIONS",
            f"proof uses disallowed declarations: {', '.join(bad_decls)}",
            verdict=answer_spec.verdict,
            artifact_path=str(art_dir),
            direct_declarations=direct_declarations,
            axioms=used_axioms,
            stdout=clean_stdout,
            stderr=clean_stderr,
        )

    return _result(
        "accepted",
        "ACCEPTED",
        "certificate accepted",
        verdict=answer_spec.verdict,
        artifact_path=str(art_dir),
        direct_declarations=direct_declarations,
        axioms=used_axioms,
        stdout=clean_stdout,
        stderr=clean_stderr,
    )
