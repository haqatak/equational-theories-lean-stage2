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

import itertools
import json
import random
import sys
import time
from typing import Dict, List, Optional, Tuple

# ══════════════════════════════════════════════════════════════
# Terms — hash-consed, so identity is structural equality
# ══════════════════════════════════════════════════════════════
_V_CACHE: Dict[str, "Term"] = {}
_A_CACHE: Dict[Tuple[int, int], "Term"] = {}
_UID = itertools.count()


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


def models_of(lhs1, rhs1, n, sample=0, cap=600, seed=0, deadline=float("inf")):
    """Magmas on Fin n satisfying eq1. Cached — repeated eq1 costs nothing."""
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
    _MODELS[key] = out
    return out


def refute(prob: Problem, deadline=float("inf"), sizes=(2, 3), sample4=0):
    """Return (n, table) with eq1 holding and eq2 failing, or None."""
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
    # No model up to size 3: SAT search for n≥4 (the hard cases).
    sizes_left = [n for n in range(4, 9) if time.time() < deadline]
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


try:
    import pycosat
    HAVE_PYCOSAT = True
except Exception:
    HAVE_PYCOSAT = False


def _sat_witness(lhs1, rhs1, lhs2, rhs2, n, eq1_vars, eq2_vars, deadline=float("inf")):
    """One size-n magma (flat row-major list) with eq1 universally true & eq2 false, else None.

    ``deadline`` bounds the search: a single UNSAT size can take ~70s, so we bail out
    if the total elapsed time crosses it. Returns a *flat* list of length n*n.
    """
    if not HAVE_PYCOSAT:
        return None
    last = time.time()

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
    lines.append(f"theorem rhs_neg : ¬ ∀ ({' '.join(va)} : E), {eq2_disp} := by")
    lines.append("  intro h")
    lines.append(f"  have h1 := h {args}")
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
                partials = [{pat.val: t} for t in side_term.subterms if t.size == 0]
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
# Candidate generation
# ══════════════════════════════════════════════════════════════
def candidates(prob: Problem, budget: float):
    """Yield (verdict, code) attempts, cheapest first."""
    t0 = time.time()

    inst = head_instance(prob)
    if inst:
        yield "true", wrap_true(inst, prob.vars2, False), "instance"

    r = refute(prob, deadline=t0 + min(30.0, budget * 0.05), sizes=(2, 3))
    if r:
        yield "false", emit_false(prob, r[0], r[1]), "refute23"

    # Triviality comes AFTER refutation: if a small model of eq1 breaks eq2
    # the answer is false and no derivation of a = b can exist anyway.
    for c in trivial_variants(prob, time.time() + min(15.0, budget * 0.03)):
        yield "true", c, "trivial"

    # Whole-goal rw search on the real goal pair (lhs2, rhs2).
    # Uses only in-scope variables, so the emitted ``have`` refs are valid.
    left = budget - (time.time() - t0)
    if left > 5:
        c = rw_search_emit(prob, time.time() + min(left * 0.2, 30.0))
        if c:
            yield "true", c, "rw_search"

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

    # The SAT refute4 fallback is the only reliable route to many FALSE
    # problems (e.g. models that only exist at n>=6), so it always gets a
    # fair slice of the remaining budget.
    left = budget - (time.time() - t0)
    if left > 5:
        r = refute(prob, deadline=t0 + budget * 0.95, sizes=(), sample4=200000)
        if r:
            yield "false", emit_false(prob, r[0], r[1]), "refute4"


# ══════════════════════════════════════════════════════════════
# Solo protocol
# ══════════════════════════════════════════════════════════════
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

    for verdict, code, _head in candidates(prob, budget):
        stdout.write(json.dumps({"call": "judge", "verdict": verdict, "code": code}) + "\n")
        stdout.flush()
        reply = stdin.readline()
        if not reply:
            return
        if json.loads(reply).get("status") == "accepted":
            return


# ══════════════════════════════════════════════════════════════
# Offline batch mode — no judge, for local iteration
# ══════════════════════════════════════════════════════════════
def batch(path, limit=0, budget=5.0, show=0):
    import collections
    rows = []
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
        ans = str(p.get("answer", "")).lower()
        if got is None:
            tally["no_answer"] += 1
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


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--batch":
        batch(sys.argv[2],
              limit=int(sys.argv[3]) if len(sys.argv) > 3 else 0,
              show=int(sys.argv[4]) if len(sys.argv) > 4 else 0)
    else:
        solo(sys.stdin, sys.stdout)