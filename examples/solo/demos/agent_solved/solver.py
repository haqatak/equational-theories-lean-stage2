#!/usr/bin/env python3
"""
SAIR Mathematics Distillation Challenge — Equational Theories, Stage 2.

Single-file solver. Standard library only.

Strategy, cheapest first:
  1. head_instance   — eq2 is a substitution instance of eq1        (~0.03 ms)
  2. head_singleton  — official Singleton.lean collapse pattern     (~0.05 ms)
  3. refute          — finite counter-model on Fin 2/3/4  => FALSE  (~0.2 ms)
  4. head_search     — one-sided rewrite search over the goal pair  => TRUE

Certificates follow the shapes in the Stage 2 README:

  TRUE   Goal = ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
  FALSE  Goal = ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G

Solo I/O: one problem JSON on stdin, {"call": "judge", ...} on stdout,
judge verdict back on stdin. Rejected proofs are retried with alternate
emission shapes before giving up.
"""
from __future__ import annotations

import gc
import itertools
import json
import multiprocessing as mp
import os
import random
import re
import signal
import sys
import time
import resource
from typing import Dict, List, Optional, Tuple

# ══════════════════════════════════════════════════════════════
# Terms — hash-consed, so identity is structural equality
# ══════════════════════════════════════════════════════════════
_V_CACHE: Dict[str, "Term"] = {}
_A_CACHE: Dict[Tuple[int, int], "Term"] = {}
_UID = itertools.count()


def _clear_term_caches():
    """Clear the hash-consing caches to bound memory across many problems.

    The caches exist to make ``A(l, r)`` return the same object for the same
    subterms (so ``is`` checks work as structural equality). They are only
    needed within a single problem's search; clearing them between problems
    prevents unbounded growth when mining creates millions of transient terms.

    Order matters: ``_REPL`` stores ``Term`` objects that reference subterms
    in ``_A_CACHE``. Clearing ``_REPL`` first frees those references, then
    clearing ``_A_CACHE``/``_V_CACHE`` frees the subterms themselves.
    """
    _REPL.clear()
    _A_CACHE.clear()
    _V_CACHE.clear()
    gc.collect()


class Term:
    __slots__ = ("val", "l", "r", "uid", "size", "_vars", "_subs", "_str")

    def __init__(self, val, l, r):
        self.val, self.l, self.r = val, l, r
        self.uid = next(_UID)
        self.size = 0 if val is not None else 1 + l.size + r.size
        self._vars = None
        self._subs = None
        self._str = None

    def __hash__(self):
        return self.uid

    def __eq__(self, other):
        return self is other

    def __lt__(self, other):
        return self.uid < other.uid

    def __str__(self):
        if self._str is None:
            self._str = self.val if self.val is not None else "(%s◇%s)" % (self.l, self.r)
        return self._str

    __repr__ = __str__

    @property
    def vars(self):
        if self._vars is None:
            self._vars = frozenset([self.val]) if self.val is not None else (self.l.vars | self.r.vars)
        return self._vars

    @property
    def subterms(self):
        if self._subs is None:
            if self.val is not None:
                self._subs = frozenset([self])
            else:
                self._subs = frozenset([self]) | self.l.subterms | self.r.subterms
        return self._subs

    def to_lean(self) -> str:
        if self.val is not None:
            return self.val
        return "(%s ◇ %s)" % (self.l.to_lean(), self.r.to_lean())


def V(name: str) -> Term:
    t = _V_CACHE.get(name)
    if t is None:
        t = _V_CACHE[name] = Term(name, None, None)
    return t


def A(l: Term, r: Term) -> Term:
    k = (l.uid, r.uid)
    t = _A_CACHE.get(k)
    if t is None:
        t = _A_CACHE[k] = Term(None, l, r)
    return t


def parse(s: str) -> Term:
    s = s.strip().replace("*", "◇").replace(" ", "")
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        d, ok = 0, True
        for i, c in enumerate(s):
            d += (c == "(") - (c == ")")
            if d == 0 and i < len(s) - 1:
                ok = False
                break
        if not ok:
            break
        s = s[1:-1]
    d, op = 0, -1
    for i, c in enumerate(s):
        if c == "(":
            d += 1
        elif c == ")":
            d -= 1
        elif c == "◇" and d == 0:
            op = i
            break
    if op >= 0:
        return A(parse(s[:op]), parse(s[op + 1:]))
    if not s or not s.isalpha():
        raise ValueError("bad term: %r" % s)
    return V(s)


def subst(t: Term, env: Dict[str, Term]) -> Term:
    if t.val is not None:
        return env.get(t.val, t)
    return A(subst(t.l, env), subst(t.r, env))


_REPL: Dict[Tuple[int, int, int], Term] = {}
_REPL_MAX = 20_000  # bounded cache: each entry holds a Term tree referencing
                    # subterms in _A_CACHE, so a large bound keeps old subterms
                    # alive even after _A_CACHE is cleared.


def replace_all(t: Term, old: Term, new: Term) -> Term:
    """Single-pass replacement of every occurrence — matches Lean `rw`."""
    if t is old:
        return new
    if t.val is not None:
        return t
    k = (t.uid, old.uid, new.uid)
    hit = _REPL.get(k)
    if hit is None:
        hit = _REPL[k] = A(replace_all(t.l, old, new), replace_all(t.r, old, new))
        # Evict oldest entry when cache exceeds bound to prevent memory blowup.
        if len(_REPL) > _REPL_MAX:
            _REPL.pop(next(iter(_REPL)))
    return hit


def match(pat: Term, t: Term, env: Optional[Dict[str, Term]] = None):
    """Non-linear match: repeated pattern variables must bind identically."""
    if env is None:
        env = {}
    stack = [(pat, t)]
    while stack:
        p, s = stack.pop()
        if p.val is not None:
            prev = env.get(p.val)
            if prev is None:
                env[p.val] = s
            elif prev is not s:
                return None
        else:
            if s.val is not None:
                return None
            stack.append((p.l, s.l))
            stack.append((p.r, s.r))
    return env


def find_redexes(pat: Term, t: Term):
    out = []
    for s in t.subterms:
        if s.val is None:
            e = match(pat, s)
            if e is not None:
                out.append((s, e))
    return out


def first_appearance(*terms: Term) -> List[str]:
    seen, out = set(), []
    for term in terms:
        stack = [term]
        while stack:
            t = stack.pop()
            if t.val is not None:
                if t.val not in seen:
                    seen.add(t.val)
                    out.append(t.val)
            else:
                stack.append(t.r)
                stack.append(t.l)
    return out


class Problem:
    def __init__(self, pid, eq1, eq2, eq1_id=0, eq2_id=0):
        self.pid, self.eq1, self.eq2 = pid, eq1, eq2
        self.eq1_id, self.eq2_id = eq1_id, eq2_id
        a, b = eq1.split("=")
        self.lhs1, self.rhs1 = parse(a), parse(b)
        a, b = eq2.split("=")
        self.lhs2, self.rhs2 = parse(a), parse(b)
        self.vars1 = first_appearance(self.lhs1, self.rhs1)
        self.vars2 = first_appearance(self.lhs2, self.rhs2)
        self.n1 = len(self.vars1)
        self.var_headed = self.lhs1.val is not None


# ══════════════════════════════════════════════════════════════
# FALSE certificates — finite counter-models
# ══════════════════════════════════════════════════════════════
def _compile(t: Term, n: int) -> str:
    if t.val is not None:
        return t.val
    return "T[%s*%d+%s]" % (_compile(t.l, n), n, _compile(t.r, n))


def _make(lhs: Term, rhs: Term, varlist: List[str], n: int, want_witness: bool):
    params = ", ".join(varlist) if varlist else "_d"
    ret = ", ".join(varlist) if varlist else "0"
    if len(varlist) == 1:
        params += ","
    if want_witness:
        src = ("def f(T, P):\n"
               "    for %s in P:\n"
               "        if %s != %s: return (%s,)\n"
               "    return None\n" % (params, _compile(lhs, n), _compile(rhs, n), ret))
    else:
        src = ("def f(T, P):\n"
               "    for %s in P:\n"
               "        if %s != %s: return False\n"
               "    return True\n" % (params, _compile(lhs, n), _compile(rhs, n)))
    ns: Dict = {}
    exec(src, ns)
    return ns["f"]


_MODELS: Dict[Tuple[str, str, int, int], List[Tuple[int, ...]]] = {}
_MODELS_MAX = 64  # bounded LRU-ish cache: evict oldest entry when full


def models_of(lhs1, rhs1, n, sample=0, cap=600, seed=0, deadline=float("inf")):
    """Magmas on Fin n satisfying eq1. Cached — repeated eq1 costs nothing.

    The cache is bounded to ``_MODELS_MAX`` entries to prevent unbounded
    memory growth across thousands of problems."""
    key = (str(lhs1), str(rhs1), n, sample)
    hit = _MODELS.get(key)
    if hit is not None:
        return hit
    vl = first_appearance(lhs1, rhs1)
    P = list(itertools.product(range(n), repeat=len(vl)))
    holds = _make(lhs1, rhs1, vl, n, False)
    out: List[Tuple[int, ...]] = []
    cells = n * n
    if sample:
        rnd = random.Random(seed)
        for _ in range(sample):
            if time.time() > deadline:
                break
            T = tuple(rnd.randrange(n) for _ in range(cells))
            if holds(T, P):
                out.append(T)
                if len(out) >= cap:
                    break
    else:
        for T in itertools.product(range(n), repeat=cells):
            if time.time() > deadline:
                break
            if holds(T, P):
                out.append(T)
                if len(out) >= cap:
                    break
    if len(_MODELS) >= _MODELS_MAX:
        _MODELS.pop(next(iter(_MODELS)))  # evict oldest
    _MODELS[key] = out
    return out


def refute(prob: Problem, deadline=float("inf"), sizes=(2, 3), sample4=0, sat=True,
           sat_sizes=(4, 5, 6, 7, 8)):
    """Return (n, table) with eq1 holding and eq2 failing, or None.

    ``sizes`` are enumerated model sizes (n=2,3 enumeration is cheap);
    ``sample4`` enables sampled n=4 search; ``sat`` enables the SAT fallback;
    ``sat_sizes`` limits which sizes the SAT phase may try."""
    plans = [(n, 0) for n in sizes]
    if sample4:
        plans.append((4, sample4))
    for n, samp in plans:
        if time.time() > deadline:
            return None
        ms = models_of(prob.lhs1, prob.rhs1, n, sample=samp, deadline=deadline)
        if not ms:
            continue
        P2 = list(itertools.product(range(n), repeat=len(prob.vars2)))
        fails = _make(prob.lhs2, prob.rhs2, prob.vars2, n, True)
        for T in ms:
            if time.time() > deadline:
                return None
            if fails(T, P2) is not None:
                return (n, T)
    if not sat:
        return None
    # No model up to the enumerated sizes: SAT search for n≥4 (the hard cases).
    sizes_left = [n for n in sat_sizes if time.time() < deadline]
    budget_per = (deadline - time.time()) / max(len(sizes_left), 1)
    for n in sizes_left:
        size_deadline = time.time() + budget_per
        t = _sat_witness(prob.lhs1, prob.rhs1, prob.lhs2, prob.rhs2,
                         n, prob.vars1, prob.vars2, deadline=size_deadline)
        if t is not None:
            return (n, tuple(int(x) for x in t))
    return None


# ─── axiom-free finite counter-models (no `decide`, no banned axioms) ───
def _eval_term(t, table, assign, n):
    """Evaluate a Term over a row-major magma table (list of lists of ints)."""
    if t.val is not None:
        return assign[t.val]
    return table[_eval_term(t.l, table, assign, n) * n + _eval_term(t.r, table, assign, n)]


class _TN:
    """Tseitin term node with a stable unique id (unlike id(), which recycles)."""
    __slots__ = ("uid", "kind", "pos", "l", "r")
    _C = itertools.count(1)
    def __init__(self, kind, pos=None, l=None, r=None):
        self.uid = next(_TN._C); self.kind = kind
        self.pos = pos; self.l = l; self.r = r


_SAT_MAX_CLAUSES = 2_000_000  # rough clause-count guard (see _sat_witness)
_CONJECTURE_CAP = 30  # max conjectures to attempt proving per problem
# Hard address-space cap (bytes) for the forked SAT child. pycosat.solve is a
# blocking C call that can run away to >130GB on a hard UNSAT instance and crash
# the whole process with a bus error/segfault. We cannot interrupt it from Python,
# so we run it in a forked child and let the OS kill it if it exceeds this cap.
# Anything above the cap is treated as "no witness at this size".
_SAT_MEM_CAP = 6 * 1024 ** 3  # ~6 GB



try:
    import pycosat
    HAVE_PYCOSAT = True
except Exception:
    HAVE_PYCOSAT = False


def _sat_solve_body(lhs1, rhs1, lhs2, rhs2, n, eq1_vars, eq2_vars, deadline):
    """Build the size-n SAT instance and search for a counter-model witness.

    Returns a flat row-major witness list, or None. This is the full SAT encoding
    (the part that used to live inside ``_sat_witness``); it lives in a forked
    child with a memory cap so a runaway UNSAT solve cannot kill the process.
    """
    def enc(t, vidx):
        if t.val is not None:
            return _TN("v", pos=vidx[t.val])
        return _TN("a", l=enc(t.l, vidx), r=enc(t.r, vidx))

    _nv = [0]
    def newvar():
        _nv[0] += 1
        return _nv[0]

    cell = [[[newvar() for _ in range(n)] for _ in range(n)] for _ in range(n)]
    clauses = []
    def add(*xs):
        clauses.append([x for x in xs if x != 0])

    for r in range(n):
        for c in range(n):
            add(*[cell[r][c][v] for v in range(n)])
            for a in range(n):
                for b in range(a + 1, n):
                    add(-cell[r][c][a], -cell[r][c][b])

    val = {}
    def vlit(term, akey, v):
        k = (term.uid, akey, v)
        if k not in val:
            val[k] = newvar()
        return val[k]

    def enforce(term, akey):
        if term.kind == "v":
            av = akey[term.pos]
            for v in range(n):
                add(vlit(term, akey, v) if v == av else -vlit(term, akey, v))
        else:
            enforce(term.l, akey); enforce(term.r, akey)
            for x in range(n):
                for y in range(n):
                    for v in range(n):
                        add(-vlit(term.l, akey, x), -vlit(term.r, akey, y),
                            -vlit(term, akey, v), cell[x][y][v])
                        add(-vlit(term.l, akey, x), -vlit(term.r, akey, y),
                            -cell[x][y][v], vlit(term, akey, v))

    vidx1 = {v: i for i, v in enumerate(eq1_vars)}
    for a1 in itertools.product(range(n), repeat=len(eq1_vars)):
        if time.time() > deadline:
            return None
        tl = enc(lhs1, vidx1); tr = enc(rhs1, vidx1)
        enforce(tl, a1); enforce(tr, a1)
        for u in range(n):
            for v in range(n):
                if u != v:
                    add(-vlit(tl, a1, u), -vlit(tr, a1, v))

    vidx2 = {v: i for i, v in enumerate(eq2_vars)}
    for a2 in itertools.product(range(n), repeat=len(eq2_vars)):
        if time.time() > deadline:
            return None
        tl = enc(lhs2, vidx2); tr = enc(rhs2, vidx2)
        enforce(tl, a2); enforce(tr, a2)
        test = clauses + [[-vlit(tl, a2, v), -vlit(tr, a2, v)] for v in range(n)]
        res = pycosat.solve(test)
        if isinstance(res, list):
            solset = set(res)
            table = [[0] * n for _ in range(n)]
            for r in range(n):
                for c in range(n):
                    for v in range(n):
                        if cell[r][c][v] in solset:
                            table[r][c] = v
            d = dict(zip(eq2_vars, a2))
            flat = [row[c] for row in table for c in range(n)]
            if _eval_term(lhs2, flat, d, n) != _eval_term(rhs2, flat, d, n):
                return flat
    return None


def _sat_witness(lhs1, rhs1, lhs2, rhs2, n, eq1_vars, eq2_vars, deadline=float("inf")):
    """One size-n magma (flat row-major list) with eq1 universally true & eq2 false, else None.

    ``deadline`` bounds the search: a single UNSAT size can take ~70s, so we bail out
    if the total elapsed time crosses it. Returns a *flat* list of length n*n.

    Memory guard (pi-hint): the SAT solve can blow past available RAM on a hard
    UNSAT instance (measured >130GB in one case) and crash the whole process with a
    bus error / segfault. pycosat.solve is a blocking C call we can't interrupt, so
    we run it in a forked child with a hard address-space cap. If the child is killed
    by the OS for exceeding it, we treat the size as "no witness" and move on.
    """
    if not HAVE_PYCOSAT:
        return None
    if time.time() > deadline:
        return None
    # Rough guard: refuse sizes whose clause count would be enormous. This catches
    # the n^n1/n^n2 blowup before we even fork; the memory cap handles the solver.
    n1, n2 = len(eq1_vars), len(eq2_vars)
    est_clauses = (n * n * n) * (n ** n1 + n ** n2) * 2
    if est_clauses > _SAT_MAX_CLAUSES:
        return None

    # SAT child -> parent transport uses a temp file, NOT mp.Queue. A forked
    # child killed mid-write on mp.Queue's background feeder/pipe can corrupt
    # shared IPC state and crash the PARENT with a native heap error
    # (``malloc: Double free``); a temp file has no shared state to corrupt.
    #
    # We use subprocess (not fork) so the child is a fully separate process:
    # fork's copy-on-write means the child's memory is accounted to the parent's
    # RSS, which made the parent appear to use 16-360GB. subprocess gives the
    # child its own address space, so the parent's RSS stays bounded.
    import tempfile, subprocess
    fd, path = tempfile.mkstemp(prefix="satwit_", dir=_tmpdir())
    os.close(fd)
    # Serialize the problem to a JSON file the child reads (avoids argv limits).
    prob_path = path + ".prob"
    with open(prob_path, "w") as f:
        json.dump({"lhs1": str(lhs1), "rhs1": str(rhs1), "lhs2": str(lhs2),
                   "rhs2": str(rhs2), "n": n, "eq1_vars": list(eq1_vars),
                   "eq2_vars": list(eq2_vars), "deadline": deadline,
                   "out": path}, f)
    try:
        proc = subprocess.run(
            [sys.executable, "-B", "-c",
             "import sys; sys.path.insert(0, %r); "
             "from solver import _sat_solve_worker_main; "
             "_sat_solve_worker_main(%r)" % (
                 os.path.dirname(os.path.abspath(__file__)), prob_path)],
            timeout=max(deadline - time.time(), 1.0),
            capture_output=True)
    except subprocess.TimeoutExpired:
        pass
    except Exception:
        pass
    finally:
        try:
            os.unlink(prob_path)
        except OSError:
            pass
    try:
        with open(path, "rb") as f:
            res = f.read()
    except Exception:
        res = b""
    try:
        os.unlink(path)
    except OSError:
        pass
    if not res:
        return None
    try:
        out = json.loads(res)
    except Exception:
        return None
    if out is None:
        return None
    return [int(x) for x in out]


def _tmpdir():
    """Workspace-independent scratch dir for SAT child handoff files."""
    d = os.path.join(os.environ.get("TMPDIR", "/tmp"), "eqsolve_sat")
    os.makedirs(d, exist_ok=True)
    return d


def _sat_solve_worker(lhs1, rhs1, lhs2, rhs2, n, eq1_vars, eq2_vars, deadline, path):
    """Child worker: run the SAT encoding under a hard memory cap and report a witness.

    Sets RLIMIT_AS (the *address space* limit — a previous version passed
    ``RUSAGE_SELF`` here, which happens to equal ``RLIMIT_CPU`` and silently
    capped CPU time at ~6 s instead of memory) before calling the blocking
    pycosat.solve, so a runaway UNSAT solve is killed by the OS rather than
    taking the parent process down. The witness (or a JSON ``null``) is
    written to ``path`` for the parent to read.
    """
    try:
        resource.setrlimit(resource.RLIMIT_AS, (_SAT_MEM_CAP, _SAT_MEM_CAP))
    except Exception:
        pass
    result = None
    try:
        result = _sat_solve_body(lhs1, rhs1, lhs2, rhs2, n, eq1_vars, eq2_vars, deadline)
    except MemoryError:
        result = None
    except BaseException:
        result = None
    try:
        with open(path, "w") as f:
            f.write(json.dumps(result))
    except Exception:
        pass


def _sat_solve_worker_main(prob_path):
    """Entry point for the subprocess SAT worker.

    Reads the problem from ``prob_path`` (JSON), sets a memory cap, runs the
    SAT encoding, and writes the witness to the output path. This is a
    standalone function so it can be invoked via ``python -c`` in a separate
    process (avoiding fork's copy-on-write memory accounting).
    """
    try:
        resource.setrlimit(resource.RLIMIT_AS, (_SAT_MEM_CAP, _SAT_MEM_CAP))
    except Exception:
        pass
    with open(prob_path) as f:
        spec = json.load(f)
    lhs1 = parse(spec["lhs1"])
    rhs1 = parse(spec["rhs1"])
    lhs2 = parse(spec["lhs2"])
    rhs2 = parse(spec["rhs2"])
    n = spec["n"]
    eq1_vars = spec["eq1_vars"]
    eq2_vars = spec["eq2_vars"]
    deadline = spec["deadline"]
    out_path = spec["out"]
    result = None
    try:
        result = _sat_solve_body(lhs1, rhs1, lhs2, rhs2, n, eq1_vars, eq2_vars,
                                 deadline)
    except MemoryError:
        result = None
    except BaseException:
        result = None
    try:
        with open(out_path, "w") as f:
            f.write(json.dumps(result))
    except Exception:
        pass


def emit_false(prob: Problem, n: int, table) -> str:
    """Axiom-free finite counter-model certificate.

    Builds an explicit inductive magma `E`, defines its operation table,
    transports `Magma.op` onto it via `op_eq : Magma.op = Eop := rfl` (plain
    rfl, NOT funext — funext pulls in the banned `Quot.sound`), then closes
    EquationLHS by case-splitting constructors and EquationRHS by exhibiting a
    single violating assignment. Zero axioms.
    """
    if isinstance(table, tuple):
        flat = list(table)
        rows = [list(flat[i * n:(i + 1) * n]) for i in range(n)]
    elif len(table) and not isinstance(table[0], int):
        # 2D: list of rows.
        rows = [list(r) for r in table]
        flat = [v for row in rows for v in row]
    else:
        # 1D: flat row-major array.
        flat = list(table)
        rows = [list(flat[i * n:(i + 1) * n]) for i in range(n)]
    n_ctors = " | ".join(f"n{i}" for i in range(n))
    lines = ["import Mathlib", "import JudgeMagma.Magma", "import JudgeProblem", ""]
    lines.append(f"inductive E | {n_ctors}")
    lines.append("")
    lines.append("def Eop (a b : E) : E :=")
    lines.append("  match a, b with")
    for i in range(n):
        for j in range(n):
            lines.append(f"    | E.n{i}, E.n{j} => E.n{rows[i][j]}")
    lines += ["", "instance : Magma E where", "  op := Eop", ""]
    lines.append("theorem op_eq : Magma.op = Eop := rfl")
    lines.append("")
    vl1 = first_appearance(prob.lhs1, prob.rhs1)
    eq1_disp = prob.eq1.replace("*", " ◇ ")
    lines.append(f"theorem lhs_magma : ∀ ({' '.join(vl1)} : E), {eq1_disp} := by")
    lines.append(f"  intro {' '.join(vl1)}")
    lines.append("  rw [op_eq]")
    if vl1:
        lines.append(f"  {' <;> '.join(f'cases {v}' for v in vl1)}")
    lines.append("  all_goals rfl")
    lines.append("")
    va = first_appearance(prob.lhs2, prob.rhs2)
    eq2_disp = prob.eq2.replace("*", " ◇ ")
    assign = None
    for combo in itertools.product(range(n), repeat=len(va)):
        a = dict(zip(va, combo))
        if _eval_term(prob.lhs2, flat, a, n) != _eval_term(prob.rhs2, flat, a, n):
            assign = a; break
    if assign is None:
        raise RuntimeError("no witness assignment for eq2")
    args = " ".join(f"E.n{assign[v]}" for v in va)
    va = first_appearance(prob.lhs2, prob.rhs2)
    eq2_disp = prob.eq2.replace("*", " ◇ ")
    assign = None
    for combo in itertools.product(range(n), repeat=len(va)):
        a = dict(zip(va, combo))
        if _eval_term(prob.lhs2, flat, a, n) != _eval_term(prob.rhs2, flat, a, n):
            assign = a; break
    if assign is None:
        raise RuntimeError("no witness assignment for eq2")
    args = " ".join(f"E.n{assign[v]}" for v in va)
    lines.append(f"theorem rhs_neg : ¬ ∀ ({' '.join(va)} : E), {eq2_disp} := by")
    lines.append("  intro h")
    lines.append(f"  have h1 := h {args}")
    # rw [op_eq] at h1 only when h1 mentions the magma op: for op-free eq2
    # (e.g. x = y) the hypothesis is already a bare constructor equation and
    # ``cases h1`` alone closes it; a vacuous rw fails to compile.
    if prob.lhs2.val is None or prob.rhs2.val is None:
        lines.append("  rw [op_eq] at h1")
    lines.append("  cases h1")
    lines.append("")
    lines.append("theorem submission : Goal :=")
    lines.append("  ⟨E, inferInstance, ⟨lhs_magma, rhs_neg⟩⟩")
    return "\n".join(lines) + "\n"


# ══════════════════════════════════════════════════════════════
# TRUE certificates
# ══════════════════════════════════════════════════════════════
def wrap_true(body: str, vars2: List[str], trailing_rfl: bool) -> str:
    vs = " ".join(vars2) if vars2 else "x"
    tail = "  rfl\n" if trailing_rfl else ""
    return ("import JudgeProblem\n\n"
            "def submission : Goal := by\n"
            "  intro G _ h %s\n%s%s" % (vs, body, tail))


class Step:
    __slots__ = ("args", "fwd", "side")

    def __init__(self, args, fwd, side):
        self.args, self.fwd, self.side = args, fwd, side

    def tactic(self) -> str:
        a = " ".join(x.to_lean() for x in self.args)
        rw = "rw [h %s]" % a if self.fwd else "rw [← h %s]" % a
        return "conv_%s => %s" % ("lhs" if self.side == 0 else "rhs", rw)


def apply_step(prob, state, st):
    env = dict(zip(prob.vars1, st.args))
    L, R = subst(prob.lhs1, env), subst(prob.rhs1, env)
    old, new = (L, R) if st.fwd else (R, L)
    if old is new:
        return None
    side = state[st.side]
    ns = replace_all(side, old, new)
    if ns is side:
        return None
    return (ns, state[1]) if st.side == 0 else (state[0], ns)


def successors(prob, state, pool, max_size):
    out, seen = [], set()

    def offer(env, fwd, ix):
        st = Step(tuple(env[v] for v in prob.vars1), fwd, ix)
        ns = apply_step(prob, state, st)
        if ns and ns not in seen and ns[0].size <= max_size and ns[1].size <= max_size:
            seen.add(ns)
            out.append((ns, st))

    for ix in (0, 1):
        side = state[ix]
        for pat, fwd in ((prob.lhs1, True), (prob.rhs1, False)):
            if pat.val is not None:
                partials = [{pat.val: t} for t in side.subterms if t.size == 0]
            else:
                partials = [e for _g, e in find_redexes(pat, side)]
            for base in partials:
                unbound = [v for v in prob.vars1 if v not in base]
                if not unbound:
                    offer(base, fwd, ix)
                elif len(unbound) <= 3:
                    for combo in itertools.product(pool, repeat=len(unbound)):
                        env = dict(base)
                        env.update(zip(unbound, combo))
                        offer(env, fwd, ix)
    return out


def mismatch(a: Term, b: Term) -> int:
    if a is b:
        return 0
    if a.val is not None or b.val is not None:
        return a.size + b.size + 1
    return mismatch(a.l, b.l) + mismatch(a.r, b.r)


def head_search(prob, deadline, beam=600, max_depth=6, max_size=24):
    start = (prob.lhs2, prob.rhs2)
    if start[0] is start[1]:
        return []
    pool = [V(v) for v in prob.vars2][:4] or [V("x")]
    frontier = [(0, start, [])]
    visited = {start}
    for _ in range(max_depth):
        if time.time() > deadline:
            break
        scored = []
        for _h, state, path in frontier:
            if time.time() > deadline:
                break
            for ns, st in successors(prob, state, pool, max_size):
                if time.time() > deadline:
                    break
                if ns in visited:
                    continue
                visited.add(ns)
                npath = path + [st]
                if ns[0] is ns[1]:
                    return verify(npath, prob)
                scored.append((mismatch(ns[0], ns[1]) + (ns[0].size + ns[1].size) // 2, ns, npath))
        if not scored:
            break
        scored.sort(key=lambda x: x[0])
        frontier = scored[:beam]
    return None


def verify(path, prob):
    """Replay the path; return it only if it really closes the goal."""
    state = (prob.lhs2, prob.rhs2)
    for st in path:
        ns = apply_step(prob, state, st)
        if ns is None:
            return None
        state = ns
    return path if state[0] is state[1] else None


def head_instance(prob) -> Optional[str]:
    for (p1, p2), flip in (((prob.lhs1, prob.rhs1), False), ((prob.rhs1, prob.lhs1), True)):
        env = match(p1, prob.lhs2)
        if env is None:
            continue
        env = match(p2, prob.rhs2, env)
        if env is None or any(v not in env for v in prob.vars1):
            continue
        args = " ".join(env[v].to_lean() for v in prob.vars1)
        return "  exact %s\n" % ("(h %s).symm" % args if flip else "h %s" % args)
    return None


def true_variants(prob, path) -> List[str]:
    """Alternate emission shapes, tried in order against the judge."""
    body = "".join("  %s\n" % st.tactic() for st in path)
    outs = [wrap_true(body, prob.vars2, True), wrap_true(body, prob.vars2, False)]
    # A whole-goal rw chain: valid whenever no step's redex occurs on the
    # other side, and shorter when it is.
    plain = "".join(
        "  rw [%sh %s]\n" % ("" if st.fwd else "← ", " ".join(a.to_lean() for a in st.args))
        for st in path)
    outs.append(wrap_true(plain, prob.vars2, False))
    return outs


def trivial_variants(prob, deadline) -> List[str]:
    """If eq1 forces a one-element magma it entails `a = b`, and that is
    something we can PROVE rather than guess: run the same search with the
    goal pair (a, b). A found path is replay-verified, so unlike a
    finite-model heuristic this cannot claim a false implication.
    (Absence of small models proves nothing -- a law can be satisfiable
    only at size 5 or only infinitely.)

    Emits whole-goal ``rw`` inside a ``have triv`` block (4-space indent).
    Safety filter: skips paths whose redex ``old`` appears as a subterm of
    the OTHER side, which would make the whole-goal ``rw`` rewrite both
    sides and diverge from the one-sided search semantics."""
    if not prob.var_headed:
        return []
    triv = Problem(prob.pid, "%s = %s" % (prob.lhs1, prob.rhs1), "a = b",
                   prob.eq1_id, prob.eq2_id)
    path = head_search(triv, deadline, beam=1500, max_depth=8, max_size=20)
    if not path:
        return []
    # Safety: the (a,b) search rewrites one side at a time. Whole-goal rw
    # rewrites BOTH sides. For the emission to be valid, no step's redex
    # ``old`` may appear as a subterm of the other side.
    a, b = V("a"), V("b")
    L, R = a, b
    for st in path:
        env = dict(zip(prob.vars1, st.args))
        Ld, Rd = subst(prob.lhs1, env), subst(prob.rhs1, env)
        old, new = (Ld, Rd) if st.fwd else (Rd, Ld)
        other = R if st.side == 0 else L
        if old in other.subterms:
            return []  # unsafe — would rewrite the other side too
        if st.side == 0:
            L = replace_all(L, old, new)
        else:
            R = replace_all(R, old, new)
    if str(L) != str(R):
        return []
    plain = "".join(
        "    rw [%sh %s]\n" % ("" if st.fwd else "\u2190 ",
                              " ".join(x.to_lean() for x in st.args))
        for st in path)
    body = ("  have triv : \u2200 (a b : G), a = b := by\n"
            "    intro a b\n%s"
            "  exact triv _ _\n" % plain)
    return [wrap_true(body, prob.vars2, False)]


def _rw_pool(prob: Problem) -> List[Term]:
    """Pool for whole-goal rw search: only in-scope vars + goal subterms."""
    out: set = set()
    def collect(t: Term) -> None:
        if id(t) in out:
            return
        out.add(t)
        if t.val is None:
            collect(t.l)
            collect(t.r)
    collect(prob.lhs2)
    collect(prob.rhs2)
    for v in prob.vars2:
        out.add(V(v))
    return list(out)


def _all_rewrites(prob: Problem, state: Tuple[Term, Term],
                  pool: List[Term], max_size: int):
    """All possible rewrites (env, old, new, fwd) applicable to the goal pair."""
    seen: set = set()
    out = []
    for side_term in (state[0], state[1]):
        for pat, fwd in ((prob.lhs1, True), (prob.rhs1, False)):
            if pat.val is not None:
                partials = [{pat.val: u} for u in side_term.subterms if u.size == 0]
            else:
                partials = [e for _g, e in find_redexes(pat, side_term)]
            for base in partials:
                unbound = [v for v in prob.vars1 if v not in base]
                if not unbound:
                    envs = [base]
                elif len(unbound) <= 3:
                    envs = []
                    for combo in itertools.product(pool, repeat=len(unbound)):
                        env = dict(base)
                        env.update(zip(unbound, combo))
                        envs.append(env)
                else:
                    continue
                for env in envs:
                    L = subst(prob.lhs1, env)
                    R = subst(prob.rhs1, env)
                    old, new = (L, R) if fwd else (R, L)
                    if old is new:
                        continue
                    if old.size > max_size or new.size > max_size:
                        continue
                    key = (str(old), str(new))
                    if key not in seen:
                        seen.add(key)
                        out.append((env, old, new, fwd))
    return out


def rw_search(prob: Problem, deadline: float, pool: List[Term],
              beam: int = 2000, max_depth: int = 16,
              max_size: int = 44) -> Optional[List]:
    """Search using whole-goal ``rw`` semantics: each step rewrites ALL
    occurrences of a redex in BOTH sides of the goal ``lhs2 = rhs2``.
    Returns a list of ``(env, old, new, fwd)`` steps, or ``None``."""
    start = (prob.lhs2, prob.rhs2)
    if str(start[0]) == str(start[1]):
        return []
    frontier = [(start, [])]
    visited = {str(start[0]) + "," + str(start[1])}
    for _ in range(max_depth):
        if time.time() > deadline:
            break
        scored = []
        for state, path0 in frontier:
            for env, old, new, fwd in _all_rewrites(prob, state, pool, max_size):
                nL = replace_all(state[0], old, new)
                nR = replace_all(state[1], old, new)
                key = str(nL) + "," + str(nR)
                if key in visited:
                    continue
                visited.add(key)
                npath = path0 + [(env, old, new, fwd)]
                if str(nL) == str(nR):
                    return npath
                scored.append((mismatch(nL, nR) + (nL.size + nR.size) // 2,
                              (nL, nR), npath))
        if not scored:
            break
        scored.sort(key=lambda x: x[0])
        frontier = [(s, p) for _h, s, p in scored[:beam]]
    return None


def rw_search_emit(prob: Problem, deadline: float) -> Optional[str]:
    """Whole-goal ``rw`` search on the real goal pair, emit the found path."""
    pool = _rw_pool(prob)
    path = rw_search(prob, deadline, pool)
    if not path:
        return None
    lines = ["  intro G _ h " + " ".join(prob.vars2)]
    for k, (env, old, new, fwd) in enumerate(path):
        args = " ".join(env[v].to_lean() for v in prob.vars1)
        lines.append("  have e%d := h %s" % (k + 1, args))
    for k, (env, old, new, fwd) in enumerate(path):
        if fwd:
            lines.append("  rw [e%d]" % (k + 1))
        else:
            lines.append("  rw [\u2190 e%d]" % (k + 1))
    return ("import JudgeProblem\n\ndef submission : Goal := by\n" +
            "\n".join(lines) + "\n")


# ══════════════════════════════════════════════════════════════
# Lemma mining — manufacture TRUE-side ammunition from FALSE-side machinery
# ══════════════════════════════════════════════════════════════
# Every magma of size 2 or 3 satisfying eq1 can be enumerated (see
# ``models_of``). An identity that fails in one of them is therefore *not* a
# theorem of eq1, while one that survives all of them is a conjecture worth
# trying: proving it turns it into a rewrite rule the goal search may use.
# This is the classic UT/Argonne move — finite models refute candidates cheaply,
# and the survivors are proved by the ordinary (sound) search, so nothing here
# ever trusts an unproved identity.
def _fresh_names(used: List[str], k: int) -> List[str]:
    out = []
    for ch in "uvwxyztq":
        if ch not in used and len(out) < k:
            out.append(ch)
    return out


def _idioms(max_size: int, names: List[str]) -> List[Term]:
    """Every term over ``names`` with 2 <= size <= max_size."""
    vs = [V(n) for n in names]
    out = list(vs)
    seen = {str(t) for t in out}
    while True:
        nxt = []
        for a in out:
            for b in out:
                t = A(a, b)
                if t.size <= max_size and str(t) not in seen:
                    seen.add(str(t))
                    nxt.append(t)
        if not nxt:
            break
        out += nxt
    return [t for t in out if t.size >= 2]


def mine_conjectures(prob: Problem, deadline: float, names: List[str],
                     max_size: int = 4, cap: int = 40):
    """Identities over ``names`` valid in every small model of eq1.

    Returns [] when no small model is known (nothing can be filtered out then).
    Bounded to ``_CONJECTURE_CAP`` results to limit downstream proof attempts."""
    ms = []
    for n in (2, 3):
        ms += [(T, n) for T in models_of(prob.lhs1, prob.rhs1, n, cap=cap,
                                         deadline=deadline)]
    if not ms:
        return []
    cands = _idioms(max_size, names)
    out = []
    for i, s in enumerate(cands):
        if time.time() > deadline or len(out) >= _CONJECTURE_CAP:
            break
        for t in cands[i + 1:]:
            if time.time() > deadline or len(out) >= _CONJECTURE_CAP:
                break
            ok = True
            for T, n in ms:
                for combo in itertools.product(range(n), repeat=len(names)):
                    a = dict(zip(names, combo))
                    if _eval_term(s, T, a, n) != _eval_term(t, T, a, n):
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                out.append((s, t))
    out.sort(key=lambda st: st[0].size + st[1].size)
    return out


def _lemma_proof(prob: Problem, s: Term, t: Term, names: List[str],
                 deadline: float, name: str):
    """Prove ``s = t`` from eq1 with head_search; return a ``have`` block.

    The block proves ``∀ (u v : G), s = t`` in the context already introduced
    by ``wrap_true``, so it may use only the outer hypothesis ``h``."""
    sub = Problem(prob.pid + "#lem", "%s=%s" % (prob.lhs1, prob.rhs1),
                  "%s=%s" % (s, t), prob.eq1_id, 0)
    ok_names = set(names)
    for beam, depth, size in ((200, 5, 20), (800, 7, 26)):
        if time.time() > deadline:
            return None
        path = head_search(sub, deadline, beam, depth, size)
        if path:
            # head_search builds step arguments from the lemma goal's own
            # variables, so every argument is a term over `names` and stays in
            # scope inside the `have` block below. Assert rather than trust.
            if any(a.vars - ok_names for st in path for a in st.args):
                return None
            body = "".join("        %s\n" % st.tactic() for st in path)
            return ("  have %s : ∀ (%s : G), %s = %s := by\n"
                    "      intro %s\n%s      rfl\n"
                    % (name, " ".join(names), s.to_lean(), t.to_lean(),
                       " ".join(names), body))
    return None


_RULE_REWRITE_CAP = 400  # max rewrites per (state, rule) to bound memory


def _rule_rewrites(rules, state, pool, max_size):
    """All (ri, args, old, new, fwd, side) rewrites of the goal pair by rules.

    Bounded by ``_RULE_REWRITE_CAP`` to prevent memory blowup on large pools."""
    out, seen = [], set()
    for ri, (lhs, rhs, rvars) in enumerate(rules):
        for ix in (0, 1):
            side = state[ix]
            for pat, repl, fwd in ((lhs, rhs, True), (rhs, lhs, False)):
                if pat.val is not None:
                    bases = [{pat.val: u} for u in side.subterms if u.size == 0]
                else:
                    bases = [e for _g, e in find_redexes(pat, side)]
                for base in bases:
                    unbound = [v for v in rvars if v not in base]
                    if len(unbound) > 3:
                        continue
                    for combo in itertools.product(pool, repeat=len(unbound)):
                        env = dict(base)
                        env.update(zip(unbound, combo))
                        old, new = (subst(lhs, env), subst(rhs, env)) if fwd \
                            else (subst(rhs, env), subst(lhs, env))
                        if old is new or old.size > max_size or new.size > max_size:
                            continue
                        key = (ri, str(old), str(new))
                        if key in seen:
                            continue
                        seen.add(key)
                        out.append((ri, tuple(env[v] for v in rvars), old, new,
                                    fwd, ix))
                        if len(out) >= _RULE_REWRITE_CAP:
                            return out
    return out


def _rule_search(prob: Problem, rules, deadline, beam=400, max_depth=6,
                 max_size=24):
    """Beam search over the goal pair using eq1 *and* proven lemmas.

    Steps are one-sided (``conv_lhs``/``conv_rhs``), so a closed path replays
    exactly like ``head_search``'s and emits with the same tactic shapes.

    Memory: uses parent pointers instead of copying full paths at each step,
    and bounds the visited set to ``beam * max_depth`` entries."""
    start = (prob.lhs2, prob.rhs2)
    if start[0] is start[1]:
        return []
    pool = [V(v) for v in prob.vars2][:4] or [V("x")]
    # parent: state -> (parent_state, step)  — avoids copying path lists
    parent = {start: None}
    frontier = [start]
    for _ in range(max_depth):
        if time.time() > deadline:
            break
        scored = []
        for state in frontier:
            if time.time() > deadline:
                break
            for ri, args, old, new, fwd, ix in _rule_rewrites(rules, state, pool,
                                                              max_size):
                side = state[ix]
                ns_side = replace_all(side, old, new)
                if ns_side is side:
                    continue
                ns = (ns_side, state[1]) if ix == 0 else (state[0], ns_side)
                if ns in parent or ns[0].size > max_size or ns[1].size > max_size:
                    continue
                parent[ns] = (state, (ri, args, fwd, ix))
                if ns[0] is ns[1]:
                    # Reconstruct path from parent pointers
                    path = []
                    cur = ns
                    while parent[cur] is not None:
                        pstate, step = parent[cur]
                        path.append(step)
                        cur = pstate
                    path.reverse()
                    return path
                scored.append((mismatch(ns[0], ns[1])
                               + (ns[0].size + ns[1].size) // 2, ns))
        if not scored:
            break
        scored.sort(key=lambda x: x[0])
        frontier = [s for _h, s in scored[:beam]]
    return None


def mined_variants(prob: Problem, deadline: float, max_lemmas: int = 6):
    """Prove small model-filtered identities, then retry the goal with them.

    Yields candidate TRUE certificates (each self-contained and judge-checkable).
    Nothing unsound can escape: a lemma is used only after ``head_search``
    produced a replay-verified derivation of it from ``h``, and the goal path is
    replayed by ``_rule_replay`` before emission."""
    used = list(prob.vars2) + list(prob.vars1) + ["G", "h"]
    names = _fresh_names(used, 2)
    if len(names) < 2:
        return
    conj = mine_conjectures(prob, min(deadline, time.time() + 20.0), names)
    if not conj:
        return
    rules = [(prob.lhs1, prob.rhs1, prob.vars1)]
    blocks = []
    for (s, t) in conj:
        if len(blocks) >= max_lemmas or time.time() > deadline:
            break
        body = _lemma_proof(prob, s, t, names, deadline, "l%d" % len(blocks))
        if body is None:
            continue
        blocks.append(body)
        rules.append((s, t, list(names)))
        # Clear transient terms created during lemma proof to bound memory.
        _clear_term_caches()
    if not blocks:
        return
    path = _rule_search(prob, rules, deadline)
    if not path:
        return
    if _rule_replay(prob, rules, path) is None:
        return
    body = "".join(blocks)
    for (ri, args, fwd, ix) in path:
        a = " ".join(x.to_lean() for x in args)
        ref = "h %s" % a if ri == 0 else "l%d %s" % (ri - 1, a)
        body += ("  conv_%s => rw [%s%s]\n"
                 % ("lhs" if ix == 0 else "rhs", "" if fwd else "← ", ref))
    yield wrap_true(body, prob.vars2, True)


def _rule_replay(prob: Problem, rules, path):
    state = (prob.lhs2, prob.rhs2)
    for (ri, args, fwd, ix) in path:
        lhs, rhs, rvars = rules[ri]
        env = dict(zip(rvars, args))
        old, new = (subst(lhs, env), subst(rhs, env)) if fwd \
            else (subst(rhs, env), subst(lhs, env))
        if old is new:
            return None
        side = state[ix]
        ns = replace_all(side, old, new)
        if ns is side:
            return None
        state = (ns, state[1]) if ix == 0 else (state[0], ns)
    return path if state[0] is state[1] else None


# ══════════════════════════════════════════════════════════════
# Candidate generation
# ══════════════════════════════════════════════════════════════


def _collapse_head(prob: Problem):
    """Return (head_var, head_side) if one side of eq1 is a lone variable
    absent from the other side; (None, None) otherwise.

    head_var absent from the other side ⟹ eq1 equates EVERY element (a = F
    and b = F for the same F) ⟹ singleton magma. Pure syntax, O(1)."""
    if prob.lhs1.val is not None and prob.lhs1.val not in prob.rhs1.vars:
        return prob.lhs1.val, 0
    if prob.rhs1.val is not None and prob.rhs1.val not in prob.lhs1.vars:
        return prob.rhs1.val, 1
    return None, None


def collapse_variants(prob: Problem):
    """Structural singleton detector ('0646 family').

    If one side of eq1 is a lone variable absent from the other side, eq1
    forces a one-element magma and ANY goal follows in five tactics. Pure
    syntax; no search, no models. Sound by construction: h is applied twice
    with IDENTICAL tail fillers, so both instantiated hypotheses mention the
    identical F-term and a = b follows by transitivity/symmetry alone.
    Verified judge-accepted on normal_0646 before wiring in."""
    head_var, side = _collapse_head(prob)
    if head_var is None:
        return []
    if not any(v != head_var for v in prob.vars1):
        return []  # eq1 is x = x — already handled elsewhere
    head_idx = prob.vars1.index(head_var)
    pool = prob.vars2 or ["x"]
    args1, args2 = [], []
    fi = 0
    for v in prob.vars1:
        if v == head_var:
            args1.append("a")
            args2.append("b")
        else:
            f = pool[fi % len(pool)]
            args1.append(f)
            args2.append(f)
            fi += 1
    ta, tb = " ".join(args1), " ".join(args2)
    # transitivity direction depends on which side the head variable is on:
    if side == 0:
        # h1 : a = F(fill), h2 : b = F(fill)  ⇒  a = b via h1.trans h2.symm
        chain = "    exact h1.trans h2.symm\n"
    else:
        # h1 : F = a, h2 : F = b  ⇒  a = b via (h1).symm.trans h2
        chain = "    exact h1.symm.trans h2\n"
    body = (
        "  have sing : ∀ (a b : G), a = b := by\n"
        "    intro a b\n"
        "    have h1 := h %s\n"
        "    have h2 := h %s\n%s"
        "  exact sing _ _\n") % (ta, tb, chain)
    return [wrap_true(body, prob.vars2, False)]


def candidates(prob: Problem, budget: float):
    """Yield (verdict, code) attempts, cheapest first."""
    t0 = time.time()
    # Env toggle for controlled experiments (default ON, production behavior):
    # SAIR_MINING=0 skips the lemma-mining phase entirely.
    mining_on = os.environ.get("SAIR_MINING", "1") != "0"

    inst = head_instance(prob)
    if inst:
        yield "true", wrap_true(inst, prob.vars2, False), "instance"

    # refutation without SAT (enumeration only): cheap, and TRUE problems
    # (no small counter-model) skip the otherwise-futile inline SAT fork.
    r = refute(prob, deadline=t0 + min(30.0, budget * 0.05), sizes=(2, 3), sat=False)
    if r:
        yield "false", emit_false(prob, r[0], r[1]), "refute23"

    # Triviality comes AFTER refutation: if a small model of eq1 breaks eq2
    # the answer is false and no derivation of a = b can exist anyway.
    for c in collapse_variants(prob):
        yield "true", c, "collapse"
    for c in trivial_variants(prob, time.time() + min(15.0, budget * 0.03)):
        yield "true", c, "trivial"
    # Clear caches after trivial_variants: head_search with beam=1500 and
    # max_depth=8 can create a large visited set of Term objects.
    _clear_term_caches()

    # Whole-goal rw search on the real goal pair (lhs2, rhs2).
    # Uses only in-scope variables, so the emitted ``have`` refs are valid.
    left = budget - (time.time() - t0)
    if left > 5:
        c = rw_search_emit(prob, time.time() + min(left * 0.2, 30.0))
        if c:
            yield "true", c, "rw_search"
        # rw_search with beam=2000 and max_depth=16 creates a large visited
        # set of Term objects; clear caches to prevent accumulation.
        _clear_term_caches()

    # Early SAT slice (n=4,5) for FALSE problems whose smallest counter-model
    # is beyond enumeration. Runs BEFORE the long proof search. The old
    # schedule did exactly this SAT work inline until the end of the
    # refute23 window, so reusing one equal extension of that window keeps
    # the TRUE-problem schedule unchanged while giving the slice a real
    # chance to fire. n=6 deliberately lives in the FINAL phase instead:
    # inside this shared window an UNSAT n=6 starves proven n=4/5 winners
    # (measured -1 net solve online), while in the final phase its cost is
    # absorbed by ~40% of the total budget. n=2,3 need no re-check here:
    # refutation above already covered them (models_of is also cached).
    left = budget - (time.time() - t0)
    sat45_end = t0 + 2.0 * min(30.0, budget * 0.05)
    if left >= min(5.0, budget * 0.4) and time.time() < sat45_end:
        r = refute(prob, deadline=sat45_end, sizes=(), sat=True,
                   sat_sizes=(4, 5))
        if r:
            yield "false", emit_false(prob, r[0], r[1]), "sat45"
        # Clear caches after SAT phase to free any transient terms.
        _clear_term_caches()

    # head_search is capped so it cannot starve the SAT-based refute4 fallback.
    search_deadline = t0 + budget * 0.55
    for beam, depth, size in ((600, 6, 24), (2000, 10, 32), (5000, 14, 40)):
        left = budget - (time.time() - t0)
        if left <= 5 or time.time() >= search_deadline:
            break
        path = head_search(prob, time.time() + min(left * 0.4, 600.0), beam, depth, size)
        if path:
            for c in true_variants(prob, path):
                yield "true", c, "search"
            break
        # Clear caches between search iterations: head_search with beam=600
        # and max_depth=6 can create millions of transient Term objects in
        # _A_CACHE/_REPL. Without clearing, they accumulate across iterations
        # and across problems, causing the 360GB memory explosion.
        _clear_term_caches()

    # Lemma mining: enumerate the small models of eq1, keep the identities they
    # do NOT refute, prove the survivors from h, and retry the goal with them as
    # extra rewrite rules. Only worth trying once the plain search has failed;
    # a FALSE problem pays at most this slice before the SAT refute below runs.
    left = budget - (time.time() - t0)
    if mining_on and left > 20:
        for c in mined_variants(prob, time.time() + min(25.0, left * 0.10)):
            yield "true", c, "mined"

    # The SAT refute4+ fallback is the only reliable route to many FALSE
    # problems (models that only exist at n>=6), so it always gets a
    # fair slice of the remaining budget. n=6 first: a witness at 6 is
    # cheap to find (measured <0.5 s) while UNSAT at 6 is expensive, and
    # the final phase has ~40% of the total budget to absorb that risk.
    left = budget - (time.time() - t0)
    if left > 5:
        r = refute(prob, deadline=t0 + budget * 0.95, sizes=(), sample4=200000,
                   sat=True, sat_sizes=(6, 4, 7, 8))
        if r:
            yield "false", emit_false(prob, r[0], r[1]), "refute4"


# ══════════════════════════════════════════════════════════════
# Solo protocol
# ══════════════════════════════════════════════════════════════

# Top-level PROMPT constant: the proxy extracts this via AST and fills its
# placeholders ({problem.*}, {history.*}, {solver.*}) before each LLM call.
# Only those placeholder shapes are filled/stripped, so the literal JSON
# braces in the examples below survive intact.
PROMPT = """You are a Lean 4 expert proving implications between equational laws
of magmas (a set with one binary operation written with the infix symbol).

Hypothesis available in context: equation1 holds, i.e. we have
  h : ForallVars (EqLHS = EqRHS)
where EqLHS and EqRHS are the two sides of equation1, and the goal is
Equation2LHS = Equation2RHS for equation2 in the same magma G.

Your task: decide whether equation1 implies equation2.
- If TRUE: give a Lean 4 tactic proof using h.
- If FALSE: produce a finite magma (Cayley table) satisfying equation1 but
  violating equation2.

Problem:
  equation1 ({problem.eq1_name}): {problem.equation1}
  equation2 ({problem.eq2_name}): {problem.equation2}

Previous judge feedback on this problem (may be empty):
{history.attempts}

Return ONLY a single JSON object, no markdown fences, no commentary:
  TRUE:  {verdict: true, proof: "..."}
  FALSE: {verdict: false, n: 5, table: [[...], ...]}
The proof field: Lean tactic lines only (intro/have/rw/conv/exact/apply/refine/
simp/cases/constructor/rfl). No 'def submission', no imports, no 'by', no
'decide'/'native_decide'/'sorry'/'Classical.choice'/'Quot.sound' (banned by the
judge). Reference the hypothesis as h and instantiate it with explicit terms:
  have h1 := h a b c
Tables: row i lists magma outputs for left operand i; cell j is op i j."""


def _llm_extract_json(text):
    """Extract a JSON object from an LLM response; None if unparseable."""
    text = re.sub(r"</think>[\s\S]*?(?:<think>|$)", "", text)
    text = re.sub(r"```(?:json)?\s*\n?", "", text).strip()
    try:
        return json.loads(text)
    except Exception:
        pass
    m = re.search(r"\{[\s\S]*\}", text)
    if m:
        try:
            return json.loads(m.group())
        except Exception:
            return None
    return None


def _llm_true_code(prob, proof_body):
    """Wrap an LLM proof body in the judge-accepted TRUE certificate shape.

    Returns None if the body is empty or oversized — never wraps unvetted
    content the judge would waste a round on."""
    body = str(proof_body or "").strip()
    if not body:
        return None
    if ":= by" in body:
        body = re.sub(r"^.*?:=\s*by\s*\n?", "", body, count=1, flags=re.DOTALL)
    body = re.sub(r"^\s*by\s+", "", body)
    body = re.sub(r"^\s*import\s+.*\n?", "", body, flags=re.MULTILINE)
    body = re.sub(r"^\s*def\s+submission[^\n]*\n?", "", body,
                  flags=re.MULTILINE).strip()
    if not body or len(body) > 40000:
        return None
    return wrap_true(body, prob.vars2, False)


def _llm_false_code(prob, tbl):
    """Validate an LLM Cayley table, then wrap it as a FALSE certificate.

    The judge is the authority, but Python-side checking here saves a Lean
    round on junk tables that violate eq1 or accidentally satisfy eq2.
    """
    import itertools as _it
    try:
        n = len(tbl)
        if n < 1 or n > 12 or any(len(r) != n for r in tbl):
            return None
        for row in tbl:
            for cell in row:
                if not isinstance(cell, int) or not 0 <= cell < n:
                    return None

        def ev(t, env):
            if t.val is not None:
                return env[t.val]
            return tbl[ev(t.l, env)][ev(t.r, env)]

        vs = sorted(prob.lhs1.vars | prob.rhs1.vars
                    | prob.lhs2.vars | prob.rhs2.vars)
        for combo in _it.product(range(n), repeat=len(vs)):
            env = dict(zip(vs, combo))
            if ev(prob.lhs1, env) != ev(prob.rhs1, env):
                return None  # table violates eq1 in Python too
        if not any(ev(prob.lhs1, dict(zip(vs, c))) == ev(prob.rhs1, dict(zip(vs, c)))
                   and ev(prob.lhs2, dict(zip(vs, c))) != ev(prob.rhs2, dict(zip(vs, c)))
                   for c in _it.product(range(n), repeat=len(vs))):
            return None  # no witnessed violation of eq2
        return emit_false(prob, n, tbl)
    except Exception:
        return None


def _llm_round(prob, stdin, stdout, rnd, note):
    """One LLM round via the proxy protocol.

    Sends {"call":"llm","context":{...}}; the proxy fills the module's PROMPT
    template ({problem.*}, {history.*}, {solver.*}) and runs the model, so the
    solver process itself never touches the network (fine inside the
    network-isolated sandbox). Parses the reply, builds a certificate, and
    submits it to the judge. Returns True iff accepted."""
    stdout.write(json.dumps({"call": "llm",
                             "context": {"round": str(rnd),
                                         "note": note}}) + "\n")
    stdout.flush()
    reply = stdin.readline()
    if not reply:
        return False
    try:
        result = json.loads(reply)
    except Exception:
        return False
    if not isinstance(result, dict) or "error" in result:
        return False
    answer = _llm_extract_json(result.get("response", ""))
    if not isinstance(answer, dict):
        return False
    verdict = answer.get("verdict")
    if verdict == "true":
        code = _llm_true_code(prob, answer.get("proof", ""))
    elif verdict == "false":
        code = _llm_false_code(prob, answer.get("table")
                               or answer.get("counterexample_table"))
    else:
        code = None
    if code is None:
        return False
    stdout.write(json.dumps({"call": "judge", "verdict": verdict,
                             "code": code}) + "\n")
    stdout.flush()
    jreply = stdin.readline()
    if not jreply:
        return False
    try:
        return json.loads(jreply).get("status") == "accepted"
    except Exception:
        return False


def solo(stdin, stdout):
    line = stdin.readline()
    if not line.strip():
        return
    msg = json.loads(line)
    p = msg["problem"]
    budget = float(msg.get("budget", {}).get("timeout_seconds", 3600)) - 30.0

    try:
        prob = Problem(p["id"], p["equation1"], p["equation2"],
                       p.get("eq1_id", 0), p.get("eq2_id", 0))
    except Exception:
        return

    t0 = time.time()
    for verdict, code, _head in candidates(prob, budget):
        stdout.write(json.dumps({"call": "judge", "verdict": verdict, "code": code}) + "\n")
        stdout.flush()
        reply = stdin.readline()
        if not reply:
            return
        if json.loads(reply).get("status") == "accepted":
            return

    # ── LLM fallback: only after every deterministic phase failed ──
    # The proxy performs the actual model call (solver stays network-free, so
    # this works in both sandbox modes). Rounds are paced by the remaining
    # wall-clock budget; SAIR_LLM=0 disables the stage entirely for A/B runs.
    if os.environ.get("SAIR_LLM", "1") != "0":
        left = budget - (time.time() - t0)
        if left > 60:
            rounds = max(1, min(6, int(left // 90)))
            for rnd in range(rounds):
                if time.time() > t0 + 0.97 * budget:
                    break
                if _llm_round(prob, stdin, stdout, rnd,
                              "deterministic phases exhausted; residual pair"):
                    return

    # Clear hash-consing caches after each problem to bound memory.
    _clear_term_caches()


# ══════════════════════════════════════════════════════════════
# Offline batch mode — no judge, for local iteration
# ══════════════════════════════════════════════════════════════
def batch(path, limit=0, budget=5.0, show=0):
    import collections
    rows = []
    noanswer_ids = []
    with open(path) as f:
        for ln in f:
            if ln.strip():
                rows.append(json.loads(ln))
    if limit:
        rows = rows[:limit]
    tally = collections.Counter()
    shown = 0
    t0 = time.time()
    for p in rows:
        try:
            prob = Problem(p["id"], p["equation1"], p["equation2"],
                           p.get("eq1_id", 0), p.get("eq2_id", 0))
        except Exception:
            tally["parse_error"] += 1
            continue
        got = None
        for verdict, code, head in candidates(prob, budget):
            got = (verdict, code, head)
            break
        # Clear hash-consing caches between problems to bound memory: the
        # mining phase can create millions of transient Term objects that
        # would otherwise accumulate across the full problem set.
        _clear_term_caches()
        ans = str(p.get("answer", "")).lower()
        if got is None:
            tally["no_answer"] += 1
            noanswer_ids.append(p["id"])
        elif ans in ("true", "false") and got[0] != ans:
            tally["WRONG/" + got[2]] += 1
            print("WRONG %s via %s: said %s, answer %s\n  eq1: %s\n  eq2: %s"
                  % (p["id"], got[2], got[0], ans, p["equation1"], p["equation2"]))
        else:
            tally["%s/%s" % (got[0], got[2])] += 1
            if shown < show:
                shown += 1
                print("── %s (%s via %s) ──\n%s" % (p["id"], got[0], got[2], got[1]))
    dt = time.time() - t0
    print("%d problems in %.1fs (%.1fms each)" % (len(rows), dt, dt / max(len(rows), 1) * 1000))
    for k, v in tally.most_common():
        print("  %-16s %d" % (k, v))
    # List unresolved problem ids so experiments can target them (A/B testing).
    # Enable with SAIR_LIST_NOANSWER=1.
    if os.environ.get("SAIR_LIST_NOANSWER") == "1":
        print("no_answer_ids: " + ",".join(noanswer_ids))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--batch":
        batch(sys.argv[2],
              limit=int(sys.argv[3]) if len(sys.argv) > 3 else 0,
              show=int(sys.argv[4]) if len(sys.argv) > 4 else 0)
    else:
        solo(sys.stdin, sys.stdout)