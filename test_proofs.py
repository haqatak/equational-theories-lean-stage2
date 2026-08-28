#!/usr/bin/env python3
"""Local proof tester — bypasses the proxy/LLM and calls verify_answer directly.

Usage:
    python3 test_proofs.py

Reads PROOFS below and tests each against the judge. Prints accepted/rejected.
"""
import json
import os
import sys
from pathlib import Path

# Ensure judge module importable
sys.path.insert(0, str(Path(__file__).resolve().parent))

from judge.verify import verify_answer, JudgeConfig, _resolve_config

# Load the 20 sample problems
PROBLEMS = {p["id"]: p for p in json.load(open("examples/problems/sample_20.json"))}

# ──────────────────────────────────────────────────────────────────────
# Candidate proofs/counterexamples for the 6 unsolved problems.
# Each entry: (problem_id, verdict, code)
# ──────────────────────────────────────────────────────────────────────
CANDIDATES = []


def add(pid, verdict, code):
    CANDIDATES.append((pid, verdict, code))


# ---------------------------------------------------------------------------
# normal_0749: Eq701 => Eq2035
#   Eq701:  x = y ◇ (x ◇ ((z ◇ w) ◇ w))
#   Eq2035: x = ((x ◇ x) ◇ x) ◇ (x ◇ x)
# ---------------------------------------------------------------------------
# Let's first try a counterexample search by brute force to determine
# whether the implication is true or false. We do that in Python below
# and inject the resulting table as a "false" certificate. If no small
# counterexample exists, we'll attempt a "true" proof.

# ---------------------------------------------------------------------------
# normal_0260: Eq1808 => Eq3695
#   Eq1808: x = (y ◇ z) ◇ ((w ◇ x) ◇ z)
#   Eq3695: x ◇ x = (y ◇ z) ◇ (x ◇ y)
# ---------------------------------------------------------------------------
# normal_0227: Eq2377 => Eq1139
#   Eq2377: x = (y ◇ (z ◇ (x ◇ w))) ◇ y
#   Eq1139: x = y ◇ ((y ◇ (z ◇ z)) ◇ z)
# ---------------------------------------------------------------------------
# normal_0126: Eq3110 => Eq4441
#   Eq3110: x = (((y ◇ x) ◇ x) ◇ z) ◇ z
#   Eq4441: x ◇ (y ◇ x) = (x ◇ z) ◇ w
# ---------------------------------------------------------------------------
# normal_0747: Eq30 => Eq3152
#   Eq30:   x = (y ◇ x) ◇ z
#   Eq3152: x = (((y ◇ y) ◇ y) ◇ y) ◇ x
# ---------------------------------------------------------------------------
# normal_0092: Eq2581 => Eq444
#   Eq2581: x = (y ◇ ((z ◇ x) ◇ w)) ◇ z
#   Eq444:  x = x ◇ (y ◇ (y ◇ (z ◇ z)))
# ---------------------------------------------------------------------------


def main():
    cfg = _resolve_config(None)
    config = JudgeConfig(
        lake_bin=cfg.lake_bin,
        lean_bin=cfg.lean_bin,
        artifact_dir=Path(".artifacts/manual_test"),
        lean_timeout_seconds=cfg.lean_timeout_seconds,
    )

    for pid, verdict, code in CANDIDATES:
        problem = PROBLEMS[pid]
        print(f"\n=== {pid} verdict={verdict} ===")
        result = verify_answer(problem, json.dumps({"verdict": verdict, "code": code}), config=config)
        print(f"  status: {result['status']}")
        print(f"  error_code: {result.get('error_code')}")
        msg = result.get("message", "")
        if msg:
            # truncate
            print(f"  message: {msg[:800]}")


if __name__ == "__main__":
    main()