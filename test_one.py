#!/usr/bin/env python3
"""Test a single Lean proof against a specific problem using the real judge."""
import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from judge.verify import verify_answer, JudgeConfig, _resolve_config

PROBLEMS = {p["id"]: p for p in json.load(open("examples/problems/sample_20.json"))}


def test_proof(pid, verdict, code):
    """Test a proof/counterexample. Returns the result dict."""
    cfg = _resolve_config(None)
    config = JudgeConfig(
        lake_bin=cfg.lake_bin,
        lean_bin=cfg.lean_bin,
        artifact_dir=Path(".artifacts/manual_test").resolve(),
        lean_timeout_seconds=cfg.lean_timeout_seconds,
    )
    problem = PROBLEMS[pid]
    raw_answer = json.dumps({"verdict": verdict, "code": code})
    result = verify_answer(problem, raw_answer, config=config)
    return result


def true_code(proof_body):
    """Wrap a proof body in the standard true-verdict template.
    proof_body should NOT include 'intro G _ h' — that's added automatically.
    """
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        + proof_body.rstrip()
        + "\n"
    )


if __name__ == "__main__":
    # normal_0747: Eq30 => Eq3152
    # Eq30: x = (y ◇ x) ◇ z  (h : ∀ x y z, x = (y ◇ x) ◇ z)
    # Eq3152: x = (((y ◇ y) ◇ y) ◇ y) ◇ x
    # Eq30 has NO models at n≤3 (only trivial 1-element), so it forces singleton.
    #
    # Key: h a b c : a = (b ◇ a) ◇ c
    # (1) h a b a : a = (b ◇ a) ◇ a, so (b ◇ a) ◇ a = a
    # (2) h a b c : a = (b ◇ a) ◇ c for ALL c, so (b ◇ a) ◇ c = a for all c
    # To show singleton: a = b
    #   h a b b : a = (b ◇ a) ◇ b
    #   h b a b : b = (a ◇ b) ◇ b  (same z = b!)
    #   h (b ◇ a) a b : (b ◇ a) = (a ◇ (b ◇ a)) ◇ b
    #   From (2) with x=a, y=b, z=b: (b ◇ a) ◇ b = a. So a = (b ◇ a) ◇ b.
    #   From (2) with x=b, y=a, z=b: (a ◇ b) ◇ b = b. So b = (a ◇ b) ◇ b.
    #   Need: (b ◇ a) ◇ b = (a ◇ b) ◇ b? That's a = b. Circular.
    #
    # Different approach: show (b ◇ a) = (a ◇ b), then a = b.
    #   h (b ◇ a) a a : (b ◇ a) = (a ◇ (b ◇ a)) ◇ a  ... by (1), (a ◇ (b◇a)) ◇ a = (b◇a). Tautology.
    # 
    # Try: h a b c gives a = (b◇a)◇c. Let's use h with x = (b◇a):
    #   h (b◇a) b' c : (b◇a) = (b' ◇ (b◇a)) ◇ c for all b',c.
    #   Set b'=a, c=a: (b◇a) = (a ◇ (b◇a)) ◇ a. By (1): (a◇(b◇a))◇a = (b◇a). Tautology.
    #   Set b'=a, c=b: (b◇a) = (a ◇ (b◇a)) ◇ b.
    #   And a = (b◇a) ◇ b (from h a b b).
    #   So a = (b◇a) ◇ b = ((a ◇ (b◇a)) ◇ b) ... hmm.
    #   Actually: a = (b◇a) ◇ b, and (b◇a) = (a◇(b◇a)) ◇ b.
    #   So a = ((a◇(b◇a)) ◇ b) ◇ b. 
    #   By (1) with x = (a◇(b◇a)), y = b: ((a◇(b◇a))◇b)◇b... no, (1) is (y◇x)◇x = x.
    #   (b ◇ (a◇(b◇a))) ◇ (a◇(b◇a)) = (a◇(b◇a)). Not helpful.
    #
    # Let me try the simplest possible approach: just use h directly.
    # Goal: x = (((y ◇ y) ◇ y) ◇ y) ◇ x
    # h says: a = (b ◇ a) ◇ c for any a,b,c.
    # Set a = x, b = ((y◇y)◇y), c = x: x = (((y◇y)◇y) ◇ x) ◇ x. Not the goal.
    # Set a = x, b = ?, c = ?: need (b ◇ x) ◇ c = (((y◇y)◇y)◇y) ◇ x.
    # So need b◇x = ((y◇y)◇y)◇y and c = x. Then result = x. ✓
    # But we need b◇x = ((y◇y)◇y)◇y. From h: ((y◇y)◇y)◇y = y (by h y ((y◇y)◇y) y... 
    #   h y b' y : y = (b' ◇ y) ◇ y. Set b' = (y◇y)◇y: y = (((y◇y)◇y) ◇ y) ◇ y.
    #   So ((y◇y)◇y) ◇ y = y? No: h y b' y gives y = (b'◇y)◇y. So (b'◇y)◇y = y.
    #   With b' = (y◇y)◇y: (((y◇y)◇y) ◇ y) ◇ y = y.
    #   That's (((y◇y)◇y)◇y) ◇ y = y, not ((y◇y)◇y)◇y = y.
    #   
    #   From (1): (b ◇ a) ◇ a = a. Set a = y, b = (y◇y): ((y◇y) ◇ y) ◇ y = y.
    #   So ((y◇y)◇y)◇y = y. ✓ (This IS (1) with a=y, b=(y◇y).)
    #   Wait: (1) says (b◇a)◇a = a. With a=y, b=(y◇y): ((y◇y)◇y)◇y = y. YES!
    #   
    # So ((y◇y)◇y)◇y = y. Goal becomes: x = y ◇ x.
    # From h: x = (b◇x)◇c for all b,c. Set b=y, c=x: x = (y◇x)◇x. Not y◇x.
    # Hmm. Need x = y◇x. 
    # From h: (y◇x)◇c = x for all c. So (y◇x) is a left-zero for x: (y◇x)◇c = x always.
    # From (1): (y◇x)◇x = x. Consistent.
    # But does x = y◇x? From h with x = y, y = ?, z = ?: y = (b◇y)◇c.
    #   y = (x◇y)◇c for all c. Set c = x: y = (x◇y)◇x.
    #   y = (x◇y)◇x and x = (y◇x)◇x (from h x y x).
    #   If x◇y = y◇x then x = y. Circular again.
    # 
    # Let me try: does (y◇x) = y? From h with a=y◇x: (y◇x) = (b◇(y◇x))◇c.
    #   Set b=y, c=x: (y◇x) = (y◇(y◇x))◇x. By (1): (y◇(y◇x))◇(y◇x) = (y◇x). Not same.
    #   From (2): (y◇x)◇c = x for all c. So (y◇x) is such that anything ◇ c with (y◇x) on left = x.
    #   But also: (b◇(y◇x))◇c = (y◇x) for all c (from h (y◇x) b c).
    #   So b◇(y◇x) is a left-zero for (y◇x): gives (y◇x) always.
    #   And y◇x is a left-zero for x: gives x always.
    #   
    #   Key: (y◇x)◇c = x for ALL c. In particular, (y◇x)◇(y◇x) = x.
    #   And b◇(y◇x) gives (y◇x) when followed by any c.
    #   So (y◇(y◇x))◇c = (y◇x) for all c. In particular (y◇(y◇x))◇x = y◇x.
    #   But also (y◇x)◇x = x (from (1) or (2)).
    #   
    #   Now: is y = y◇x? 
    #   y = (b◇y)◇c for all b,c. Set b = y◇x, c = anything: y = ((y◇x)◇y)◇c.
    #   But (y◇x)◇y = x (from (2) with a=x, b=y, z=y: (y◇x)◇y = x).
    #   So y = (x)◇c for all c. I.e., x◇c = y for all c! ... (3)
    #   Similarly, x = (b◇x)◇c for all b,c. Set b = x, c = anything: x = (x◇x)◇c.
    #   From (3): x◇c = y, so x◇x = y. Then x = y◇c for all c. ... (4)
    #   From (3): x◇c = y for all c. From (4): y◇c = x for all c.
    #   Now: x = y◇c (from 4) and y = x◇c (from 3) for all c.
    #   Set c = x in (4): x = y◇x. Set c = y in (3): y = x◇y.
    #   From (1): (y◇x)◇x = x. But y◇x = x (from 4 with c=x). So x◇x = x.
    #   From (3) with c=x: x◇x = y. So y = x. DONE!
    #
    # So the proof chain is:
    # (1) h a b a : (b◇a)◇a = a   [specialize z=a]
    # (2) h a b c : (b◇a)◇c = a   [general form]
    # (3) h a b c with a=y, b=(y◇x), z=y: ((y◇x)◇y) = x, then h y x c: y = x◇c
    #     Actually: h y (y◇x) y : y = ((y◇x)◇y)◇y. And (y◇x)◇y = x (from h x y y).
    #     So y = x◇y. More generally, h y (y◇x) c : y = ((y◇x)◇y)◇c = x◇c. So x◇c = y. (3)
    # (4) h x x c : x = (x◇x)◇c. From (3): x◇x = y. So x = y◇c. (4)
    # (5) From (4) with c=x: x = y◇x. From (3) with c=x: x◇x = y. From (4): x = y◇x.
    #     From (1) with a=x, b=y: (y◇x)◇x = x. But y◇x = x (from 4). So x◇x = x.
    #     From (3) with c=x: x◇x = y. So y = x.
    #
    # Let me write this in Lean:
    
    pid = "normal_0747"
    
    # Goal: ∀ (x y : G), x = (((y ◇ y) ◇ y) ◇ y) ◇ x
    # h : ∀ (x y z : G), x = (y ◇ x) ◇ z
    #
    # Step 1: (b ◇ a) ◇ a = a  [h a b a]
    # Step 2: (y ◇ x) ◇ y = x  [h x y y, i.e. x = (y◇x)◇y]
    # Step 3: x ◇ c = y for all c
    #   h y (y◇x) c : y = ((y◇x)◇y)◇c = x◇c  [using step 2]
    # Step 4: x◇x = y  [step 3 with c=x]
    # Step 5: x = y◇c for all c
    #   h x x c : x = (x◇x)◇c = y◇c  [using step 4]
    # Step 6: y◇x = x  [step 5 with c=x]
    # Step 7: x◇x = x  [step 6: y◇x = x, and (y◇x)◇x = x from step 1, so x◇x = x]
    #   Actually: (y◇x)◇x = x (step 1 with a=x, b=y). y◇x = x (step 6). So x◇x = x.
    # Step 8: y = x  [step 4: x◇x = y, step 7: x◇x = x, so y = x]
    # Step 9: ((y◇y)◇y)◇y = y  [step 1 with a=y, b=(y◇y)]
    # Step 10: Goal x = (((y◇y)◇y)◇y)◇x = y◇x = x  [steps 9, 6, and y=x]
    
    proof = """  intro x y
  -- h : ∀ (a b c : G), a = (b ◇ a) ◇ c
  -- (b ◇ a) ◇ a = a  [from h a b a]
  have h1 : ∀ (a b : G), (b ◇ a) ◇ a = a := fun a b => (h a b a).symm
  -- (y ◇ x) ◇ y = x  [from h x y y]
  have h2 : (y ◇ x) ◇ y = x := (h x y y).symm
  -- x ◇ c = y for all c
  have h3 : ∀ (c : G), x ◇ c = y := fun c => by
    have := h y (y ◇ x) c
    rw [h2] at this
    exact this.symm
  -- x ◇ x = y
  have h4 : x ◇ x = y := h3 x
  -- x = y ◇ c for all c
  have h5 : ∀ (c : G), x = y ◇ c := fun c => by
    have := h x x c
    rw [h4] at this
    exact this
  -- y ◇ x = x
  have h6 : y ◇ x = x := (h5 x).symm
  -- x ◇ x = x  [h1 x y : (y◇x)◇x = x, rewrite y◇x → x]
  have h7 : x ◇ x = x := by
    have := h1 x y
    rw [h6] at this
    exact this
  -- y = x
  have h8 : y = x := by rw [← h4]; exact h7
  -- Goal: x = (((y ◇ y) ◇ y) ◇ y) ◇ x
  -- ((y ◇ y) ◇ y) ◇ y = y  [h1 y (y◇y)]
  -- So goal = y ◇ x = x  [h6]
  have h9 : ((y ◇ y) ◇ y) ◇ y = y := h1 y (y ◇ y)
  rw [h9, h6]"""
    
    code = true_code(proof)
    print(f"Testing {pid}...")
    print(f"Code:\n{code}")
    result = test_proof(pid, "true", code)
    print(f"Status: {result['status']}")
    print(f"Error: {result.get('error_code')}")
    msg = result.get("message", "")
    if msg:
        print(f"Message: {msg[:1500]}")