"""
agent_improved — Hybrid deterministic + LLM solver.

Strategy:
  Stage 1: Brute-force counterexample on Fin 2–7 with structured tables
  Stage 2: Singleton detection (Eq30 pattern) → produces valid Lean proof
  Stage 3: Enhanced LLM call with MATCH-COLLAPSE method and worked examples

Key improvement over baseline: robust singleton detection that produces
compilable Lean code, plus a more informative LLM prompt.
"""

PROMPT = """You are solving equational theory problems in Lean 4.

## Problem

Hypothesis (Eq{problem.eq1_id}): {problem.equation1}
Goal        (Eq{problem.eq2_id}): {problem.equation2}

## Analysis

This hypothesis forces every element to equal a fixed expression:
  {problem.equation1}

Variables in LHS of hyp: {solver.lhs_vars}
Variables in RHS of hyp: {solver.rhs_vars}

The variable '{solver.focal_var}' appears only on the LHS.
This means the RHS is CONSTANT in {solver.focal_var}.
Derive independence by varying just that variable:
  (h {solver.arg_list}).symm.trans (h {solver.arg_list_alt})

## Strategy

Since brute-force counterexample search failed, we suspect this implication
is TRUE. The hypothesis is very strong — it forces the magma to be
effectively a singleton (or trivially degenerate).

## MATCH-COLLAPSE Method

For proving equations of the form x = complicated_expression:

1. INTRO all variables from the goal
2. Use `h` with clever substitutions to match subterms
3. Use constancy lemmas `(h ...).symm.trans (h ...)` to collapse junk terms
4. Chain everything together in a calc proof

## Worked Example

For equation x = (y ◇ z) ◇ w implying x = x ◇ x:
- The hyp forces every element to equal (y◇z)◇w for all y,z
- This means any term with 2+ variables is constant
- Use h repeatedly with different arguments to show equality

## Previous Attempts

{history.attempts}

Respond with ONLY valid JSON:
{"verdict": "true", "proof": "<Lean tactic body>"}

Rules:
- Use ◇ (U+25C7), NOT * for the magma operator
- Proof = tactic body only, NO theorem statement
- Allowed tactics: intro, exact, calc, have, congr_arg, .symm, .trans
"""


import json
import re
import sys
from itertools import product


# ── Protocol helpers ─────────────────────────────────────────────

def read_message():
    """Read one JSON message from stdin."""
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line.strip())


def send_message(msg):
    """Write one JSON message to stdout."""
    print(json.dumps(msg), flush=True)


def call_judge(verdict, code):
    """Send a judge request and return the response."""
    send_message({"call": "judge", "verdict": verdict, "code": code})
    return read_message()


def call_llm(context):
    """Send an LLM request with solver context."""
    send_message({"call": "llm", "context": context})
    return read_message()


# ── Equation parsing & brute-force ───────────────────────────────

def parse_equation(text):
    variables = []
    seen = set()
    for v in re.findall(r'\b([a-z])\b', text):
        if v not in seen:
            seen.add(v)
            variables.append(v)
    lhs_str, rhs_str = text.split('=', 1)

    def _to_expr(s):
        s = s.strip()
        while len(s) >= 2 and s[0] == '(' and s[-1] == ')':
            depth = 0
            matched = True
            for i, c in enumerate(s):
                if c == '(':
                    depth += 1
                elif c == ')':
                    depth -= 1
                if depth == 0 and i < len(s) - 1:
                    matched = False
                    break
            if matched:
                s = s[1:-1].strip()
            else:
                break
        depth = 0
        last_op = -1
        for i, c in enumerate(s):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
            elif c == '\u25c7' and depth == 0:
                last_op = i
        if last_op >= 0:
            left = _to_expr(s[:last_op])
            right = _to_expr(s[last_op+1:])
            return lambda env, l=left, r=right: env['op'](l(env), r(env))
        s = s.strip()
        if len(s) == 1 and s in seen:
            return lambda env, v=s: env[v]
        raise ValueError(f"Cannot parse: {s}")

    return variables, _to_expr(lhs_str), _to_expr(rhs_str)


def search_counterexample(eq1_text, eq2_text, max_n=7):
    """Brute-force counterexample on Fin 2..max_n."""
    lhs_vars, lhs_l, lhs_r = parse_equation(eq1_text)
    rhs_vars, rhs_l, rhs_r = parse_equation(eq2_text)

    def check_eq(variables, lhs_fn, rhs_fn, n, op):
        for vals in product(range(n), repeat=len(variables)):
            env = {'op': op}
            for v, val in zip(variables, vals):
                env[v] = val
            if lhs_fn(env) != rhs_fn(env):
                return False
        return True

    # Structured tables to try (simplified from opnorm)
    def structured_tables(n):
        yield [[0]*n for _ in range(n)]           # constant 0
        yield [[n-1]*n for _ in range(n)]         # constant last
        yield [[i]*n for i in range(n)]           # left projection
        yield [[j for j in range(n)] for _ in range(n)]  # right projection
        if n >= 2:
            yield [[(i+j)%n for j in range(n)] for i in range(n)]  # addition mod n
        if n >= 3:
            yield [[(i*j)%n for j in range(n)] for i in range(n)]  # mult mod n

    for n in range(2, max_n + 1):
        for table in structured_tables(n):
            op = lambda a, b, t=table: t[a][b]
            lhs_ok = check_eq(lhs_vars, lhs_l, lhs_r, n, op)
            rhs_ok = check_eq(rhs_vars, rhs_l, rhs_r, n, op)
            if lhs_ok and not rhs_ok:
                return n, table

    # Also try the simple exhaustive search for small n
    for n in range(2, min(max_n + 1, 4)):
        total = n ** (n * n)
        for enc in range(min(total, 100000)):  # cap at 100K
            table = [[(enc // (n ** (i * n + j))) % n for j in range(n)] for i in range(n)]
            op = lambda a, b, t=table: t[a][b]
            lhs_ok = check_eq(lhs_vars, lhs_l, lhs_r, n, op)
            rhs_ok = check_eq(rhs_vars, rhs_l, rhs_r, n, op)
            if lhs_ok and not rhs_ok:
                return n, table

    return None, None


# ── Singleton detection ────────────────────────────────────────

def try_singleton_proof(problem, eq1_text, eq2_text):
    """Detect singleton magma pattern and produce a valid Lean proof.
    
    Pattern: hyp has form x = (y ◇ ...) ◇ ... where x only appears on LHS.
    This forces the magma to be a singleton, making any equation trivially true.
    """
    parts = eq1_text.split('=', 1)
    if len(parts) != 2:
        return None
    
    lhs_var = parts[0].strip()
    rhs_expr = parts[1].strip()
    
    # Check if x only appears on LHS (not in RHS expression)
    rhs_vars = set(re.findall(r'\b([a-z])\b', rhs_expr))
    
    if lhs_var not in rhs_vars:
        # Singleton pattern detected!
        eq2_parts = eq2_text.split('=', 1)
        if len(eq2_parts) == 2:
            goal_lhs = eq2_parts[0].strip()
            goal_rhs = eq2_parts[1].strip()
            
            # Count free variables in hyp (all except the focal x)
            all_vars = set(re.findall(r'\b([a-z])\b', eq1_text))
            free_vars = [v for v in all_vars if v != lhs_var]
            filler = "a"  # single filler variable
            
            proof = (
                f"intro {' '.join(free_vars)}\n"
                f"have singleton : \u2200 (a b : G), a = b := "
                f"fun a b => (h a {filler}).trans (h b {filler}).symm\n"
                f"exact singleton ({goal_lhs}) ({goal_rhs})"
            )
            
            code = (
                "import JudgeProblem\n"
                "def submission : Goal := by\n"
                f"  {proof}\n"
            )
            return code
    
    return None


# ── Extract JSON from LLM response ──────────────────────────────

def extract_json(text):
    """Extract JSON from LLM response, stripping markdown and comments."""
    text = re.sub(r"<think>[\s\S]*?</think>", "", text).strip()
    text = re.sub(r"^```(?:json)?\s*\n?", "", text)
    text = re.sub(r"\n?\```\s*$", "", text)
    try:
        return json.loads(text.strip())
    except Exception:
        pass
    m = re.search(r"\{[\s\S]*\}", text)
    if m:
        try:
            return json.loads(m.group())
        except Exception:
            pass
    return None


# ── Main solver logic ───────────────────────────────────────────

def main():
    """Main solver entry point."""
    # Read startup message from proxy
    startup = read_message()
    problem = startup["problem"]

    eq1_text = problem["equation1"]
    eq2_text = problem["equation2"]

    print(f"Problem: {problem['id']}", file=sys.stderr)
    print(f"  Hypothesis: {eq1_text}", file=sys.stderr)
    print(f"  Goal:       {eq2_text}", file=sys.stderr)

    # Stage 1: Brute-force counterexample search on small finite magmas
    print("  Stage 1: Counterexample search...", file=sys.stderr)
    n, table = search_counterexample(eq1_text, eq2_text, max_n=7)
    if n is not None:
        code = (
            "import JudgeProblem\n"
            "import JudgeDecide.DecideBang\n"
            "import JudgeFinOp.MemoFinOp\n"
            "open MemoFinOp\n\n"
            "def submission : Goal := by\n"
            f"  let m : Magma (Fin {n}) := {{\n"
            f"    op := finOpTable \"{json.dumps(table)}\"\n"
            f"   }}\n"
            f"  refine \u27e8Fin {n}, m, ?_\u27e9\n"
            f"  decideFin!\n"
        )
        result = call_judge("false", code)
        if result.get("status") == "accepted":
            print("  -> Solved via counterexample!", file=sys.stderr)
            return

    # Stage 2: Singleton proof pattern
    print("  Stage 2: Singleton detection...", file=sys.stderr)
    singleton_code = try_singleton_proof(problem, eq1_text, eq2_text)
    if singleton_code is not None:
        result = call_judge("true", singleton_code)
        if result.get("status") == "accepted":
            print("  -> Solved via singleton proof!", file=sys.stderr)
            return

    # Stage 3: LLM-assisted proof generation with enhanced prompt
    print("  Stage 3: LLM-assisted proof...", file=sys.stderr)
    
    # Build context for LLM
    eq1_vars = sorted(set(re.findall(r'\b([a-z])\b', eq1_text)))
    eq2_vars = sorted(set(re.findall(r'\b([a-z])\b', eq2_text)))
    parts = eq1_text.split('=', 1)
    if len(parts) == 2:
        lhs_var = parts[0].strip()
        rhs_expr = parts[1].strip()
        rhs_vars_set = set(re.findall(r'\b([a-z])\b', rhs_expr))
        focal_var = lhs_var if lhs_var not in rhs_vars_set else None
    else:
        focal_var = None
    
    # Build LLM context
    context_vars = {
        "eq1_id": problem["eq1_id"],
        "eq2_id": problem["eq2_id"],
        "equation1": eq1_text,
        "equation2": eq2_text,
        "lhs_vars": ", ".join(eq1_vars),
        "rhs_vars": ", ".join(sorted(rhs_vars_set)),
        "focal_var": focal_var or "x",
        "arg_list": "x a b c d e".split(" ")[:len(eq1_vars)],
    }

    # Use first available arg list, replace x with a, b, c...
    filler = " ".join(["a", "b", "c", "d", "e"][:len(eq1_vars)])
    
    context = {
        "round": "0",
        "solver": {
            "lhs_vars": ", ".join(eq1_vars),
            "rhs_vars": ", ".join(sorted(rhs_vars_set)),
            "focal_var": focal_var or "x",
            "arg_list": filler,
            "arg_list_alt": "a a b c d".split(" ")[:len(eq1_vars)],
        }
    }

    rnd = 0
    while True:
        context["round"] = str(rnd)
        llm_result = call_llm(context)

        if "error" in llm_result:
            print(f"  LLM error at round {rnd}", file=sys.stderr)
            break

        response_text = llm_result.get("response", "")
        answer = extract_json(response_text)
        if answer is None:
            print(f"  No JSON extracted from LLM round {rnd}", file=sys.stderr)
            rnd += 1
            continue

        verdict = answer.get("verdict")
        if verdict not in ("true", "false"):
            print(f"  Invalid verdict {verdict} at round {rnd}", file=sys.stderr)
            rnd += 1
            continue

        if verdict == "true":
            proof_body = answer.get("proof", "")
            if not proof_body:
                print(f"  No proof body at round {rnd}", file=sys.stderr)
                rnd += 1
                continue
            # Clean proof body
            if ":= by" in proof_body:
                proof_body = re.sub(r"^.*?:=\s*by\s*\n?", "", proof_body, count=1, flags=re.DOTALL)
            proof_body = re.sub(r"^\s*by\s+", "", proof_body)
            
            code = (
                "import JudgeProblem\n"
                "def submission : Goal := by\n"
                f"  intro G _ h\n"
                f"{proof_body}\n"
            )
        else:
            tbl = answer.get("counterexample_table")
            if not tbl or not isinstance(tbl, list):
                print(f"  Invalid counterexample at round {rnd}", file=sys.stderr)
                rnd += 1
                continue
            code = (
                "import JudgeProblem\n"
                "import JudgeDecide.DecideBang\n"
                "import JudgeFinOp.MemoFinOp\n"
                "open MemoFinOp\n\n"
                "def submission : Goal := by\n"
                f"  let m : Magma (Fin {len(tbl)}) := {{\n"
                f"    op := finOpTable \"{json.dumps(tbl)}\"\n"
                f"   }}\n"
                f"  refine \u27e8Fin {len(tbl)}, m, ?_\u27e9\n"
                f"  decideFin!\n"
            )

        result = call_judge(verdict, code)
        if result.get("status") == "accepted":
            print(f"  -> Solved at round {rnd}!", file=sys.stderr)
            return
        
        # Judge rejected - add feedback to context for next round
        if "round" not in context:
            context["round"] = str(rnd)
        context.setdefault("history", []).append({
            "verdict": verdict,
            "result": result.get("status"),
            "error": result.get("message", ""),
        })
        print(f"  Round {rnd} rejected: {result.get('status')}: {result.get('message', '')}", file=sys.stderr)


if __name__ == "__main__":
    main()
