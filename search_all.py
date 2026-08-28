#!/usr/bin/env python3
"""Brute-force search for counterexamples to determine true/false for each problem."""
import json
import re
from itertools import product


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
            right = _to_expr(s[last_op + 1:])
            return lambda env, l=left, r=right: env['op'](l(env), r(env))
        s = s.strip()
        if len(s) == 1 and s in seen:
            return lambda env, v=s: env[v]
        raise ValueError(f"Cannot parse: {s}")

    return variables, _to_expr(lhs_str), _to_expr(rhs_str)


def check_eq(variables, lhs_fn, rhs_fn, n, op):
    for vals in product(range(n), repeat=len(variables)):
        env = {'op': op}
        for v, val in zip(variables, vals):
            env[v] = val
        if lhs_fn(env) != rhs_fn(env):
            return False
    return True


def search(eq1_text, eq2_text, max_n=5):
    lhs_vars, lhs_l, lhs_r = parse_equation(eq1_text)
    rhs_vars, rhs_l, rhs_r = parse_equation(eq2_text)

    # First: exhaustive for n=2 (2^4=16) and n=3 (3^9=19683)
    for n in range(2, min(max_n + 1, 4)):
        total = n ** (n * n)
        for enc in range(total):
            table = [[(enc // (n ** (i * n + j))) % n for j in range(n)] for i in range(n)]
            op = lambda a, b, t=table: t[a][b]
            lhs_ok = check_eq(lhs_vars, lhs_l, lhs_r, n, op)
            rhs_ok = check_eq(rhs_vars, rhs_l, rhs_r, n, op)
            if lhs_ok and not rhs_ok:
                return n, table

    # For larger n: try structured tables (constant, projections, etc.)
    for n in range(2, max_n + 1):
        for table in _structured_tables(n):
            op = lambda a, b, t=table: t[a][b]
            lhs_ok = check_eq(lhs_vars, lhs_l, lhs_r, n, op)
            rhs_ok = check_eq(rhs_vars, rhs_l, rhs_r, n, op)
            if lhs_ok and not rhs_ok:
                return n, table
    return None, None


def _structured_tables(n):
    yield [[0] * n for _ in range(n)]           # constant 0
    yield [[n - 1] * n for _ in range(n)]       # constant last
    yield [[i] * n for i in range(n)]           # left projection
    yield [list(range(n)) for _ in range(n)]    # right projection
    if n >= 2:
        yield [[(i + j) % n for j in range(n)] for i in range(n)]   # add mod n
    if n >= 3:
        yield [[(i * j) % n for j in range(n)] for i in range(n)]   # mul mod n
    # XOR-like for n=2
    if n == 2:
        yield [[0, 1], [1, 0]]
    # "absorbing" tables: a*0=0, 0*a=0 for all a
    for const in range(n):
        t = [[const] * n for _ in range(n)]
        for i in range(n):
            t[i][const] = const
            t[const][i] = const
        yield t


problems = json.load(open("examples/problems/sample_20.json"))
unsolved = ['normal_0749', 'normal_0260', 'normal_0227', 'normal_0126', 'normal_0747', 'normal_0092']

for p in problems:
    if p['id'] not in unsolved:
        continue
    print(f"\n=== {p['id']} ===")
    print(f"  Eq1 ({p['eq1_id']}): {p['equation1']}")
    print(f"  Eq2 ({p['eq2_id']}): {p['equation2']}")
    n, table = search(p['equation1'], p['equation2'], max_n=4)
    if n is not None:
        print(f"  COUNTEREXAMPLE found at n={n}: {table}")
    else:
        print(f"  No counterexample up to n=4 → likely TRUE")