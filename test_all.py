#!/usr/bin/env python3
"""Test proofs for multiple problems."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from judge.verify import verify_answer, JudgeConfig, _resolve_config

PROBLEMS = {p["id"]: p for p in json.load(open("examples/problems/sample_20.json"))}


def test_proof(pid, verdict, code):
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


def tc(proof_body):
    """Wrap proof body in true-verdict template."""
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        + proof_body.rstrip()
        + "\n"
    )


# ──────────────────────────────────────────────────────────────────────
# normal_0749: Eq701 => Eq2035
#   Eq701:  x = y ◇ (x ◇ ((z ◇ w) ◇ w))    [h : ∀ x y z w, x = y ◇ (x ◇ ((z◇w)◇w))]
#   Eq2035: x = ((x ◇ x) ◇ x) ◇ (x ◇ x)    [goal: ∀ x, x = ((x◇x)◇x) ◇ (x◇x)]
#
# No models at n≤3 → forces singleton.
# Key: y ◇ (x ◇ ((z◇w)◇w)) = x for ALL y,z,w.
# So for any d of the form x◇((z◇w)◇w), we have y◇d = x for all y.
# To show a=b: need to find a chain.
# ──────────────────────────────────────────────────────────────────────

PROOFS = {
    # ══════════════════════════════════════════════════════════════════
    # normal_0747: SOLVED
    # ══════════════════════════════════════════════════════════════════
    "normal_0747": {
        "verdict": "true",
        "code": tc("""  intro x y
  have h1 : ∀ (a b : G), (b ◇ a) ◇ a = a := fun a b => (h a b a).symm
  have h2 : (y ◇ x) ◇ y = x := (h x y y).symm
  have h3 : ∀ (c : G), x ◇ c = y := fun c => by
    have := h y (y ◇ x) c
    rw [h2] at this
    exact this.symm
  have h4 : x ◇ x = y := h3 x
  have h5 : ∀ (c : G), x = y ◇ c := fun c => by
    have := h x x c
    rw [h4] at this
    exact this
  have h6 : y ◇ x = x := (h5 x).symm
  have h7 : x ◇ x = x := by
    have := h1 x y
    rw [h6] at this
    exact this
  have h8 : y = x := by rw [← h4]; exact h7
  have h9 : ((y ◇ y) ◇ y) ◇ y = y := h1 y (y ◇ y)
  rw [h9, h6]"""),
    },

    # ══════════════════════════════════════════════════════════════════
    # normal_0749: Eq701 => Eq2035
    # ══════════════════════════════════════════════════════════════════
    "normal_0749": {
        "verdict": "true",
        "code": tc("""  intro x
  -- h : ∀ (a b c d : G), a = b ◇ (a ◇ ((c ◇ d) ◇ d))
  -- Key: y ◇ (x ◇ ((z◇w)◇w)) = x for ALL y,z,w.
  -- So for d = x◇((z◇w)◇w), we have y◇d = x for all y.
  -- To prove: x = ((x◇x)◇x) ◇ (x◇x)
  -- Let d = x◇((x◇x)◇x). Then y◇d = x for all y.
  -- Goal RHS = ((x◇x)◇x) ◇ (x◇x). This is y◇(x◇x) where y=(x◇x)◇x.
  -- We need y◇(x◇x) = x. Is x◇x of the form a◇((z◇w)◇w)?
  -- x◇x = x◇((x◇x)◇x)? No, (z◇w)◇w with z=x,w=x gives (x◇x)◇x, not x.
  -- Actually: set z=x, w=x in h: x = y◇(x◇((x◇x)◇x)). So y◇(x◇((x◇x)◇x)) = x for all y.
  -- Set y = (x◇x)◇x: ((x◇x)◇x) ◇ (x◇((x◇x)◇x)) = x.
  -- Goal is ((x◇x)◇x) ◇ (x◇x). So need x◇((x◇x)◇x) = x◇x.
  -- From h with a = x◇x: x◇x = y◇((x◇x)◇((z◇w)◇w)) for all y,z,w.
  --   Set y=x, z=x, w=x: x◇x = x◇((x◇x)◇((x◇x)◇x)).
  --   But we need x◇x = x◇((x◇x)◇x). Different!
  -- 
  -- Actually let me just try: h x y z w gives x = y◇(x◇((z◇w)◇w)).
  -- Set x=x, y=((x◇x)◇x), z=x, w=x:
  --   x = ((x◇x)◇x) ◇ (x ◇ ((x◇x)◇x))
  -- Goal: x = ((x◇x)◇x) ◇ (x◇x)
  -- So need: x ◇ ((x◇x)◇x) = x ◇ x.
  -- From h with a = x◇((x◇x)◇x), call it e:
  --   e = y◇(e◇((z◇w)◇w)) for all y,z,w.
  -- And x = ((x◇x)◇x) ◇ e (from above).
  -- Also from h with a = x◇x:
  --   x◇x = y◇((x◇x)◇((z◇w)◇w)) for all y,z,w.
  -- 
  -- Hmm, this is hard. Let me try singleton approach instead.
  -- Since no models at n≤3, try to show all elements equal.
  -- h a b c d : a = b◇(a◇((c◇d)◇d))
  -- h b a c d : b = a◇(b◇((c◇d)◇d))
  -- Set c=a, d=a: (c◇d)◇d = (a◇a)◇a. Call this p.
  --   a = b◇(a◇p) and b = a◇(b◇p).
  --   Also h p b' c' d' : p = b'◇(p◇((c'◇d')◇d')).
  --   Set b'=a, c'=a, d'=a: p = a◇(p◇p). And p = (a◇a)◇a.
  --   So (a◇a)◇a = a◇(p◇p) = a◇(((a◇a)◇a)◇((a◇a)◇a)).
  --   From h with x=(a◇a)◇a, y=a, z=(a◇a)◇a, w=(a◇a)◇a:
  --     (a◇a)◇a = a◇(((a◇a)◇a) ◇ ((((a◇a)◇a)◇(a◇a)◇a)◇((a◇a)◇a)))
  --   This is getting too nested.
  --
  -- Let me try the simplest approach: just directly use h to rewrite the goal.
  -- h x ((x◇x)◇x) x x : x = ((x◇x)◇x) ◇ (x ◇ ((x◇x)◇x))
  -- Need: x◇((x◇x)◇x) = x◇x.
  -- h (x◇x) a b c : x◇x = a ◇ ((x◇x) ◇ ((b◇c)◇c)).
  --   Set a=x, b=x, c=x: x◇x = x ◇ ((x◇x) ◇ ((x◇x)◇x)).
  --   Not what we need.
  -- h (x◇((x◇x)◇x)) a b c : x◇((x◇x)◇x) = a◇((x◇((x◇x)◇x))◇((b◇c)◇c)).
  --   Set a=x, b=x, c=x: x◇((x◇x)◇x) = x◇((x◇((x◇x)◇x))◇((x◇x)◇x)).
  --   Not helpful either.
  --
  -- Maybe just show singleton. For any a,b:
  -- h a b a a : a = b◇(a◇((a◇a)◇a)). Call p = (a◇a)◇a.
  --   a = b◇(a◇p)  for all b.  ... (I)
  -- h b a a a : b = a◇(b◇((a◇a)◇a)) = a◇(b◇p).
  --   b = a◇(b◇p)  ... (II)
  -- h p b a a : p = b◇(p◇((a◇a)◇a)) = b◇(p◇p).
  --   p = b◇(p◇p) for all b.  ... (III)
  -- From (I): a = b◇(a◇p). Set b=a: a = a◇(a◇p). ... (IV)
  -- From (II): b = a◇(b◇p). Set b=a: a = a◇(a◇p). Same as (IV). 
  -- From (I): a = b◇(a◇p). Set b=p: a = p◇(a◇p). ... (V)
  -- From (III): p = b◇(p◇p). Set b=a: p = a◇(p◇p). ... (VI)
  -- From (I): a = b◇(a◇p) for ALL b. So b◇(a◇p) = a, meaning
  --   for d = a◇p, b◇d = a for all b. ... (VII)
  -- Similarly from (II): a◇(b◇p) = b for all b. ... (VIII)
  --   (VIII) says: a◇e = b where e = b◇p. So a◇(b◇p) = b.
  --   In particular: a◇(a◇p) = a (from IV). And a◇(b◇p) = b.
  --   So a◇(a◇p) = a and a◇(b◇p) = b.
  --   If a◇p = b◇p then a = b (from VIII).
  --   From (VII): b◇(a◇p) = a for all b. Set b=b: b◇(a◇p) = a.
  --   From (VII): b◇(b◇p) = b for all b (set a=b in VII: b◇(b◇p) = b).
  --   So b◇(a◇p) = a and b◇(b◇p) = b.
  --   If a◇p = b◇p then a = b. But do we know a◇p = b◇p?
  --   From (VII) with d = a◇p: y◇d = a for all y. 
  --   From (VII) with a→b, d = b◇p: y◇(b◇p) = b for all y.
  --   So y◇(a◇p) = a and y◇(b◇p) = b for all y.
  --   Set y = a: a◇(a◇p) = a and a◇(b◇p) = b. (both from VIII actually)
  --   Set y = b: b◇(a◇p) = a and b◇(b◇p) = b.
  --   Set y = p: p◇(a◇p) = a and p◇(b◇p) = b.
  --   From h p y z w: p = y◇(p◇((z◇w)◇w)). Set z=a,w=a: p = y◇(p◇p).
  --     So y◇(p◇p) = p for all y. ... (IX)
  --   From (VII): for d = a◇p, y◇d = a for all y.
  --   Is p◇p = a◇p? From (IX): y◇(p◇p) = p. From (VII): y◇(a◇p) = a.
  --   If p◇p = a◇p then p = a. 
  --   From (VI): p = a◇(p◇p). From (IV): a = a◇(a◇p).
  --   If p◇p = a◇p then p = a◇(p◇p) = a◇(a◇p) = a. So p = a.
  --   Then (a◇a)◇a = p = a. And from (VII) with d = a◇p = a◇a:
  --     y◇(a◇a) = a for all y.
  --   From h a◇a y z w: a◇a = y◇((a◇a)◇((z◇w)◇w)).
  --     Set z=a, w=a: a◇a = y◇((a◇a)◇p) = y◇((a◇a)◇a) = y◇p (since p=a, wait p=(a◇a)◇a).
  --     a◇a = y◇((a◇a)◇p). And (a◇a)◇p = (a◇a)◇((a◇a)◇a).
  --     From h ((a◇a)◇a) y z w: (a◇a)◇a = y◇(((a◇a)◇a)◇((z◇w)◇w)).
  --       Set z=a◇a, w=a: ((a◇a)◇a) = y◇(p◇(((a◇a)◇a)◇a)).
  --       p = y◇(p◇(p◇a)). If p=a, then a = y◇(a◇(a◇a)).
  --     This is getting circular.
  --
  -- OK let me just try a completely different, simpler approach.
  -- h a b c d : a = b ◇ (a ◇ ((c ◇ d) ◇ d))
  -- Note: for any a, and any c,d: let q = (c◇d)◇d.
  --   a = b ◇ (a ◇ q) for all b. So b◇(a◇q) = a for all b.
  --   In particular: a◇(a◇q) = a (set b=a). ... (*)
  --   And: for any b1,b2: b1◇(a◇q) = b2◇(a◇q) = a. So ◇ is "constant in first arg" when second arg is a◇q.
  --   
  --   Now: h (a◇q) b c' d' : a◇q = b◇((a◇q)◇((c'◇d')◇d')).
  --     Set c'=c, d'=d: a◇q = b◇((a◇q)◇q).
  --     But from (*): a◇(a◇q) = a. And b◇(a◇q) = a for all b.
  --     So a◇q = b◇((a◇q)◇q) for all b. Set b=a: a◇q = a◇((a◇q)◇q).
  --     From (*): a◇(a◇q) = a. So if (a◇q)◇q = a◇q, then a◇q = a◇(a◇q) = a.
  --     Is (a◇q)◇q = a◇q? From h (a◇q) b c d: a◇q = b◇((a◇q)◇q).
  --       Set b = a◇q: a◇q = (a◇q)◇((a◇q)◇q). Hmm.
  --       From h q b c d: q = b◇(q◇((c◇d)◇d)). Set c'=c, d'=d: q = b◇(q◇q).
  --         So b◇(q◇q) = q for all b. ... (**)
  --       Now: (a◇q)◇q. Is this equal to q◇q? From h: a = b◇(a◇q). Set b=q: a = q◇(a◇q).
  --         So q◇(a◇q) = a. And from (**): q◇(q◇q) = q.
  --         If a◇q = q◇q then a = q. Hmm.
  --       From h q a c d: q = a◇(q◇q). From (**): b◇(q◇q) = q, so a◇(q◇q) = q. Consistent.
  --       From h a q c d: a = q◇(a◇q). 
  --       From (VII): b◇(a◇q) = a for all b, so q◇(a◇q) = a. Consistent.
  --
  -- I think the key insight is: b◇(a◇q) = a for ALL b, and b◇(q◇q) = q for ALL b.
  -- So if a◇q = q◇q then a = q.
  -- And a◇q = b◇((a◇q)◇q) for all b (from h (a◇q) b c d with c'=c,d'=d).
  -- And q = b◇(q◇q) for all b. So if (a◇q)◇q = q◇q then a◇q = q.
  -- But is (a◇q)◇q = q◇q?
  -- From h (a◇q) b q q: (a◇q) = b◇((a◇q)◇(q◇q)). Set b=q: a◇q = q◇((a◇q)◇(q◇q)).
  -- From (**): q◇(q◇q) = q. So if (a◇q)◇(q◇q) = q◇q then a◇q = q◇(q◇q) = q.
  -- Is (a◇q)◇(q◇q) = q◇q? Hmm, getting nested again.
  --
  -- Let me just try the proof in Lean and iterate.
  --
  -- Actually, let me try the simplest possible thing: just use h directly.
  -- Goal: x = ((x◇x)◇x) ◇ (x◇x)
  -- h x ((x◇x)◇x) x x : x = ((x◇x)◇x) ◇ (x ◇ ((x◇x)◇x))
  -- So if I can show x◇((x◇x)◇x) = x◇x, I'm done.
  -- 
  -- h (x◇x) x (x◇x) (x◇x) : x◇x = x ◇ ((x◇x) ◇ (((x◇x)◇(x◇x))◇(x◇x)))
  -- That's not x◇((x◇x)◇x) either.
  --
  -- Wait. h (x◇((x◇x)◇x)) b c d : x◇((x◇x)◇x) = b◇((x◇((x◇x)◇x))◇((c◇d)◇d))
  -- Set b=x, c=x, d=x: x◇((x◇x)◇x) = x◇((x◇((x◇x)◇x))◇((x◇x)◇x))
  -- From h x x x x: x = x◇(x◇((x◇x)◇x)). So x◇((x◇x)◇x) = x... wait:
  --   h x x x x : x = x ◇ (x ◇ ((x◇x)◇x))
  --   So x◇(x◇((x◇x)◇x)) = x.
  --   And x◇((x◇x)◇x) = x◇((x◇((x◇x)◇x))◇((x◇x)◇x)).
  --   From h x x x x: x = x◇(x◇((x◇x)◇x)). So x◇((x◇x)◇x) is some element.
  --   Set c=(x◇x)◇x, d=(x◇x)◇x in h: (c◇d)◇d = (((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x).
  --   Too complex.
  --
  -- I think the right approach is just to prove singleton and then use it.
  -- Let me try: show a=b for arbitrary a,b.
  -- h a b a a : a = b◇(a◇((a◇a)◇a)). Let p = (a◇a)◇a.
  --   So a = b◇(a◇p) for all b. ... (A)
  -- h b a a a : b = a◇(b◇((a◇a)◇a)) = a◇(b◇p). ... (B)
  -- h p b a a : p = b◇(p◇((a◇a)◇a)) = b◇(p◇p) for all b. ... (C)
  -- From (A): b◇(a◇p) = a for all b. In particular p◇(a◇p) = a. ... (D)
  -- From (C): b◇(p◇p) = p for all b. In particular a◇(p◇p) = p. ... (E)
  -- From (A) with b=a: a = a◇(a◇p). ... (F)
  -- From (B) with a→a, b→b: b = a◇(b◇p). In particular a = a◇(a◇p). Same as (F).
  -- From (B): a◇(b◇p) = b. Set b=p: a◇(p◇p) = p. Same as (E).
  -- From (A): b◇(a◇p) = a. Set b=b: b◇(a◇p) = a.
  -- From (B): a◇(b◇p) = b. Set a=a, b=a: a◇(a◇p) = a. Same as (F).
  --
  -- Now: from (A), b◇(a◇p) = a for all b.
  --       from (B), a◇(b◇p) = b for all b (well, for the specific a).
  --       from (C), b◇(p◇p) = p for all b.
  --
  -- Key: from (A) with b = p: p◇(a◇p) = a. ... (D)
  --       from (C) with b = a: a◇(p◇p) = p. ... (E)
  --       from (A) with b = a: a◇(a◇p) = a. ... (F)
  --       from (C) with b = p: p◇(p◇p) = p. ... (G)
  --
  -- Now: from (B): a◇(b◇p) = b. Set b = a◇p: a◇((a◇p)◇p) = a◇p. ... (H)
  --   But is (a◇p)◇p = a◇p? From h (a◇p) b a a: a◇p = b◇((a◇p)◇p).
  --     Set b = a◇p: a◇p = (a◇p)◇((a◇p)◇p). Hmm.
  --   From (A) with d→a◇p (but p = (a◇a)◇a, can we change p?):
  --     Actually p is fixed as (a◇a)◇a. The q in the equation varies with c,d.
  --
  -- I think I need a different variable. Let me use c=b, d=b instead:
  -- h a b b b : a = b◇(a◇((b◇b)◇b)). Let q = (b◇b)◇b.
  --   a = b◇(a◇q). ... (A')
  -- h b a b b : b = a◇(b◇((b◇b)◇b)) = a◇(b◇q). ... (B')
  -- From (A'): b◇(a◇q) = a. ... (A')
  -- From (B'): a◇(b◇q) = b. ... (B')
  -- h q b' b b : q = b'◇(q◇((b◇b)◇b)) = b'◇(q◇q). ... (C')
  -- From (A') with b→a: a◇(a◇q) = a. ... (F')
  -- From (C') with b'→a: a◇(q◇q) = q. ... (E')
  -- From (A'): b◇(a◇q) = a. From (B'): a◇(b◇q) = b.
  --   Set b=a in (B'): a◇(a◇q) = a. Same as (F').
  --   Set a=b in (A'): b◇(b◇q) = b. ... (F'')
  --   From (A') with b→q: q◇(a◇q) = a. ... (D')
  --   From (C') with b'→b: b◇(q◇q) = q. ... (E'')
  --
  -- Now: from (B'): a◇(b◇q) = b. Set b = q: a◇(q◇q) = q. Same as (E').
  --   From (A'): b◇(a◇q) = a. Set a→q, b→a: a◇(q◇q) = q. Wait, (A') is b◇(a◇q)=a, 
  --   set a→q: b◇(q◇q) = q for all b. That's (E'').
  --   
  --   From (B'): a◇(b◇q) = b. Set b such that b◇q = q◇q: then a◇(q◇q) = b, so b = q (from E').
  --   So if b◇q = q◇q then b = q.
  --   From (F''): b◇(b◇q) = b. From (E''): b◇(q◇q) = q.
  --   Set b = a in (E''): a◇(q◇q) = q (same as E').
  --   Set b = q in (E''): q◇(q◇q) = q (same as G).
  --
  --   From (B'): a◇(b◇q) = b. This means a applied to (b◇q) gives b.
  --   From (F''): b◇(b◇q) = b. This means b applied to (b◇q) gives b.
  --   So a◇(b◇q) = b◇(b◇q) = b. Both give b.
  --   This means a◇e = b◇e whenever e = b◇q. 
  --   But also a◇(b◇q) = b and b◇(b◇q) = b, so a and b agree on e=b◇q.
  --
  --   From (A'): b◇(a◇q) = a. From (F'): a◇(a◇q) = a.
  --   So b◇(a◇q) = a◇(a◇q) = a. Both give a.
  --   This means b and a agree on e=a◇q.
  --
  --   Now: from (B'): a◇(b◇q) = b. From (A'): b◇(a◇q) = a.
  --   Apply (B') with b→a: a◇(a◇q) = a (F'). Apply (A') with b→b: b◇(a◇q) = a.
  --   So a and b applied to (a◇q) both give a.
  --   Apply (A') with a→b: b◇(b◇q) = b (F''). Apply (B') with b→b: a◇(b◇q) = b.
  --   So a and b applied to (b◇q) both give b.
  --
  --   Now: h a◇q b' c d: a◇q = b'◇((a◇q)◇((c◇d)◇d)).
  --     Set c=b, d=b: a◇q = b'◇((a◇q)◇q). ... (H')
  --     Set b'=a: a◇q = a◇((a◇q)◇q). 
  --     From (F'): a◇(a◇q) = a. So if (a◇q)◇q = a◇q, then a◇q = a.
  --     Is (a◇q)◇q = a◇q? From (H') with b'→(a◇q): a◇q = (a◇q)◇((a◇q)◇q).
  --       From (A') with a→(a◇q), b→(a◇q): (a◇q)◇((a◇q)◇q) = a◇q.
  --       Wait, (A') says b◇(a◇q) = a. With a→(a◇q), b→(a◇q): (a◇q)◇((a◇q)◇q) = (a◇q).
  --       But that's what (H') says! So (H') with b'→(a◇q) is just (A') applied to a◇q.
  --     From (E''): b◇(q◇q) = q. Set b = a◇q: (a◇q)◇(q◇q) = q.
  --     From (A') with a→q, b→(a◇q): (a◇q)◇(q◇q) = q. Same thing!
  --
  --   I'm going in circles. Let me try yet another substitution.
  --   h a b c d with c=a, d=b: a = b◇(a◇((a◇b)◇b)). Let r = (a◇b)◇b.
  --     a = b◇(a◇r). ... (A'')
  --   h b a b a: b = a◇(b◇((b◇a)◇a)). Let s = (b◇a)◇a.
  --     b = a◇(b◇s). ... (B'')
  --   From (A''): b◇(a◇r) = a. From (B''): a◇(b◇s) = b.
  --   From (A'') with b→a: a◇(a◇r) = a. From (B'') with a→b: b◇(b◇s) = b.
  --   h r b' a b: r = b'◇(r◇((a◇b)◇b)) = b'◇(r◇r). ... (C'')
  --   h s b' b a: s = b'◇(s◇((b◇a)◇a)) = b'◇(s◇s). ... (D'')
  --   From (C''): b◇(r◇r) = r. From (D''): a◇(s◇s) = s.
  --   
  --   Now: r = (a◇b)◇b, s = (b◇a)◇a. If I can show r = s, then from 
  --   (A''): a = b◇(a◇r) and (B''): b = a◇(b◇s) = a◇(b◇r).
  --   From (A''): b◇(a◇r) = a. From h a◇r b'' c d: a◇r = b''◇((a◇r)◇((c◇d)◇d)).
  --     Set c=a, d=b: a◇r = b''◇((a◇r)◇r).
  --     Set b''=b: a◇r = b◇((a◇r)◇r). From (A''): b◇(a◇r) = a.
  --     So a◇r = b◇((a◇r)◇r). And a = b◇(a◇r). So a◇r = b◇((a◇r)◇r).
  --     From (C''): b◇(r◇r) = r. So if (a◇r)◇r = r◇r then a◇r = r.
  --     From (A'') with a→r, b→a◇r: (a◇r)◇(r◇r) = r. 
  --       Wait, (A'') is b◇(a◇r) = a, so with a→r: b◇(r◇r) = r. That's (C'').
  --       With a→a◇r: b◇((a◇r)◇r) = a◇r. So b◇((a◇r)◇r) = a◇r. ... (I)
  --     From (I): b◇((a◇r)◇r) = a◇r. And from (C''): b◇(r◇r) = r.
  --       If (a◇r)◇r = r◇r then a◇r = r.
  --     From (A'') with a→(a◇r)◇r, b→b: b◇(((a◇r)◇r)◇r) = (a◇r)◇r. ... (J)
  --     Getting too deep.
  --
  -- I'll just try submitting various proof attempts to Lean and iterate.
  -- The simplest approach: use h directly and hope rw works.
  
  -- Attempt 1: Direct approach
  -- h x ((x◇x)◇x) x x : x = ((x◇x)◇x) ◇ (x ◇ ((x◇x)◇x))
  -- Need: x ◇ ((x◇x)◇x) = x ◇ x
  -- h (x◇x) x (x◇x) x : x◇x = x ◇ ((x◇x) ◇ (((x◇x)◇x)◇x))
  -- Not the same. Let me try:
  -- h (x◇((x◇x)◇x)) x x x : x◇((x◇x)◇x) = x ◇ ((x◇((x◇x)◇x)) ◇ ((x◇x)◇x))
  -- From h x x x x: x = x ◇ (x ◇ ((x◇x)◇x)). So x◇(x◇((x◇x)◇x)) = x.
  -- So x◇((x◇x)◇x) = x◇((x◇((x◇x)◇x))◇((x◇x)◇x)). Not helpful.
  --
  -- Let me try to prove singleton with a simpler chain.
  -- h a b c d : a = b◇(a◇((c◇d)◇d))
  -- h a b a b : a = b◇(a◇((a◇b)◇b)). Let e = (a◇b)◇b.
  --   a = b◇(a◇e). ... (1)
  -- h b a b a : b = a◇(b◇((b◇a)◇a)). Let f = (b◇a)◇a.
  --   b = a◇(b◇f). ... (2)
  -- h e b' a b : e = b'◇(e◇((a◇b)◇b)) = b'◇(e◇e). ... (3)
  -- h f b' b a : f = b'◇(f◇((b◇a)◇a)) = b'◇(f◇f). ... (4)
  -- From (1): b◇(a◇e) = a. From (2): a◇(b◇f) = b.
  -- From (1) with b→a: a◇(a◇e) = a. ... (5)
  -- From (2) with a→b: b◇(b◇f) = b. ... (6)
  -- From (3) with b'→a: a◇(e◇e) = e. ... (7)
  -- From (4) with b'→b: b◇(f◇f) = f. ... (8)
  -- From (1) with b→e: e◇(a◇e) = a. ... (9)
  -- From (3) with b'→b: b◇(e◇e) = e. ... (10)
  -- From (2) with a→f: f◇(b◇f) = b. Wait, (2) is a◇(b◇f) = b. With a→f: f◇(b◇f) = b. ... (11)
  -- From (4) with b'→a: a◇(f◇f) = f. ... (12)
  --
  -- From (1): b◇(a◇e) = a. From (10): b◇(e◇e) = e.
  --   If a◇e = e◇e then a = e.
  -- From (7): a◇(e◇e) = e. From (5): a◇(a◇e) = a.
  --   If e◇e = a◇e then e = a (from (7): a◇(a◇e) = e, from (5): a◇(a◇e) = a, so e = a).
  --   So if e◇e = a◇e then e = a, and then from (1): b◇(a◇a) = a. (since e=a)
  --   And from (3): b◇(a◇a) = a (since e=a, e◇e = a◇a). Consistent.
  --   So if e = a: from (1) b◇(a◇a) = a. From (2): a◇(b◇f) = b. 
  --     e = (a◇b)◇b = a. So (a◇b)◇b = a.
  --     f = (b◇a)◇a. From (2): a◇(b◇f) = b.
  --     From (8): b◇(f◇f) = f. From (12): a◇(f◇f) = f.
  --     From (2) with a→f: f◇(b◇f) = b. And a◇(b◇f) = b. So a and f agree on (b◇f).
  --     From (4): b'◇(f◇f) = f for all b'. So f◇f is a right-zero giving f.
  --     Similarly from (3): b'◇(e◇e) = e = a for all b'. So a◇a is a right-zero giving a.
  --     From (1) with e=a: b◇(a◇a) = a for all b. So b'◇(a◇a) = a for all b'. (matches (3) with e=a)
  --     From (2): a◇(b◇f) = b. Set b→a: a◇(a◇f) = a. 
  --       From (5): a◇(a◇e) = a, and e=a, so a◇(a◇a) = a. 
  --       So a◇(a◇f) = a and a◇(a◇a) = a. If a◇f = a◇a then... hmm.
  --     From (2): a◇(b◇f) = b. Set b→f: a◇(f◇f) = f (same as (12)).
  --     From (12): a◇(f◇f) = f. From (4): b'◇(f◇f) = f for all b'.
  --       So a◇(f◇f) = f and b◇(f◇f) = f.
  --     From (1) with e=a: b◇(a◇a) = a for all b.
  --     From (3) with e=a: b'◇(a◇a) = a for all b'. Same.
  --     So a◇a is a universal right-zero giving a, and f◇f is a universal right-zero giving f.
  --     If a◇a = f◇f then a = f. 
  --     From (2): a◇(b◇f) = b. Set b such that b◇f = a◇a: then a◇(a◇a) = b, so b = a (from a◇(a◇a)=a).
  --       So if b◇f = a◇a then b = a. In particular, set b = a: a◇f = a◇a? Then a = a. Tautology.
  --     From (2): a◇(b◇f) = b. From (6): b◇(b◇f) = b.
  --       So a◇(b◇f) = b◇(b◇f) = b. a and b agree on (b◇f).
  --     From (1) with e=a: b◇(a◇a) = a. From (6): b◇(b◇f) = b.
  --       If a◇a = b◇f then a = b. 
  --       a◇a = b◇f? From (2): a◇(b◇f) = b. From (5) with e=a: a◇(a◇a) = a.
  --         If b◇f = a◇a then b = a (from a◇(b◇f) = b and a◇(a◇a) = a).
  --         So we need to show a◇a = b◇f to conclude a = b, but that's what we're trying to prove.
  --
  -- I think I need to use the fact that b◇(a◇e) = a for ALL b (from (1)).
  -- This means the function "◇(a◇e)" is constant, always returning a.
  -- Similarly b◇(e◇e) = e for all b (from (3)).
  -- If a◇e = e◇e, then a = e (since b◇(a◇e) = a and b◇(e◇e) = e).
  --
  -- So the key question: is a◇e = e◇e?
  -- From (5): a◇(a◇e) = a. From (7): a◇(e◇e) = e.
  -- From (1) with b→a: a◇(a◇e) = a. From (3) with b'→a: a◇(e◇e) = e.
  -- h (a◇e) b' c d: a◇e = b'◇((a◇e)◇((c◇d)◇d)).
  --   Set c=a, d=b: a◇e = b'◇((a◇e)◇e). Set b'=a: a◇e = a◇((a◇e)◇e).
  --   From (5): a◇(a◇e) = a. So if (a◇e)◇e = a◇e, then a◇e = a.
  --   Is (a◇e)◇e = a◇e? From (1) with a→(a◇e)◇e... no, (1) is b◇(a◇e) = a.
  --     (1) with a→(a◇e): b◇((a◇e)◇e) = a◇e. ... (13)
  --     So (a◇e)◇e is a right-zero giving a◇e. And e◇e is a right-zero giving e (from (3)).
  --     If (a◇e)◇e = e◇e then a◇e = e.
  --     From (13): b◇((a◇e)◇e) = a◇e for all b. From (3): b◇(e◇e) = e for all b.
  --       If (a◇e)◇e = e◇e then a◇e = e.
  --       From (1): b◇(a◇e) = a. If a◇e = e then b◇e = a for all b.
  --       From (3): b◇(e◇e) = e. If a◇e = e then e = a◇e, so e◇e = (a◇e)◇e.
  --         And b◇((a◇e)◇e) = a◇e = e (from (13) and a◇e = e).
  --         And b◇(e◇e) = e (from (3)). Consistent.
  --       So a◇e = e → b◇e = a for all b → a = b (set b=a: a◇e = a, and e = a◇e, so e = a; then b◇a = a for all b; 
  --         from (2): a◇(b◇f) = b; if f = a (by symmetry) then a◇(b◇a) = b; and b◇a = a, so a◇a = b; 
  --         then from (5): a◇(a◇a) = a, so a◇b = a, and from a◇a = b: a◇b = a is a◇(a◇a) = a, consistent.)
  --
  -- So the proof outline for singleton:
  -- 1. Define e = (a◇b)◇b (for given a,b)
  -- 2. From h: b◇(a◇e) = a (for all b) ... (1)
  -- 3. From h: b◇(e◇e) = e (for all b) ... (3)
  -- 4. From h: b◇((a◇e)◇e) = a◇e (for all b) ... (13)
  -- 5. If a◇e = e◇e then a = e (from (1) and (3))
  -- 6. If (a◇e)◇e = e◇e then a◇e = e (from (13) and (3))
  -- 7. If a◇e = e then a = e (step 5 with a◇e = e◇e... wait, need a◇e = e◇e not a◇e = e)
  --    Actually if a◇e = e, then a = e (from (1): b◇e = a, from (3): b◇(e◇e) = e; 
  --    but we need a = e, which follows from (1) with b=e: e◇(a◇e) = a, and a◇e = e: e◇e = a;
  --    from (3) with b=e: e◇(e◇e) = e; so e◇a = e; from (1) with b→e: e◇(a◇e) = a, a◇e=e: e◇e = a;
  --    so a = e◇e; from (3): b◇(e◇e) = e, so b◇a = e for all b; from (1): b◇(a◇e) = a, a◇e=e: b◇e = a;
  --    so b◇e = a and b◇a = e for all b. Set b=a: a◇e = a, so e = a (since a◇e = e). Wait, a◇e = e and a◇e = a, so e = a.)
  --
  -- This is getting very complex. Let me just try a simpler approach in Lean:
  -- Try to show singleton by showing a = b using h a b _ _ and h b a _ _.
  -- The simplest: h a b a a : a = b◇(a◇((a◇a)◇a)) and h b a a a : b = a◇(b◇((a◇a)◇a)).
  -- Let p = (a◇a)◇a. Then a = b◇(a◇p) and b = a◇(b◇p).
  -- Also h p _ _ _ : p = _◇(p◇_). Set p = (a◇a)◇a.
  -- h p b a a: p = b◇(p◇((a◇a)◇a)) = b◇(p◇p). So b◇(p◇p) = p.
  -- h a b a a: a = b◇(a◇p). So b◇(a◇p) = a.
  -- If a◇p = p◇p then a = p. Then (a◇a)◇a = a, and b◇(a◇a) = a (from b◇(a◇p)=a with p=a: b◇(a◇a)=a).
  -- Then from h b a b b: b = a◇(b◇((b◇b)◇b)). Let q=(b◇b)◇b. b = a◇(b◇q).
  -- By symmetry, if b◇q = q◇q then b = q, and a◇(b◇b) = b.
  -- Then a = b◇(a◇a) and b = a◇(b◇b). Set a=b: a = a◇(a◇a). And a = b◇(a◇a) = a◇(a◇a) (if b=a). Circular.
  --
  -- OK I'll just try many things in Lean. Let me start with a proof that uses h directly.
  
  -- DIRECT: Try to prove the goal using h directly
  -- h x y z w : x = y ◇ (x ◇ ((z ◇ w) ◇ w))
  -- Goal: x = ((x ◇ x) ◇ x) ◇ (x ◇ x)
  -- Set in h: a=x, b=((x◇x)◇x), c=x, d=x: x = ((x◇x)◇x) ◇ (x ◇ ((x◇x)◇x))
  -- So need: x◇((x◇x)◇x) = x◇x.
  -- From h with a = x◇x, b = x, c = x, d = x: x◇x = x ◇ ((x◇x) ◇ ((x◇x)◇x))
  -- From h with a = x◇((x◇x)◇x), b = x, c = x, d = x: 
  --   x◇((x◇x)◇x) = x ◇ ((x◇((x◇x)◇x)) ◇ ((x◇x)◇x))
  -- Hmm. Let me try:
  -- h (x◇x) x x x : x◇x = x ◇ ((x◇x) ◇ ((x◇x)◇x))
  -- So (x◇x)◇((x◇x)◇x) appears. Call it r. x◇x = x◇r.
  -- h (x◇((x◇x)◇x)) x x x : x◇((x◇x)◇x) = x ◇ ((x◇((x◇x)◇x)) ◇ ((x◇x)◇x))
  --   So x◇((x◇x)◇x) = x◇(x◇((x◇x)◇x) ◇ ((x◇x)◇x)). Let s = x◇((x◇x)◇x).
  --   s = x◇(s◇((x◇x)◇x)). And x = ((x◇x)◇x)◇s (from h x ((x◇x)◇x) x x).
  --   Goal: x = ((x◇x)◇x)◇(x◇x). We have x = ((x◇x)◇x)◇s. So need s = x◇x.
  --   s = x◇(s◇((x◇x)◇x)). And x◇x = x◇r where r = (x◇x)◇((x◇x)◇x).
  --   If s◇((x◇x)◇x) = r then s = x◇r = x◇x. 
  --   s = x◇((x◇x)◇x), r = (x◇x)◇((x◇x)◇x).
  --   s◇((x◇x)◇x) = (x◇((x◇x)◇x))◇((x◇x)◇x). And r = (x◇x)◇((x◇x)◇x).
  --   So need (x◇((x◇x)◇x))◇((x◇x)◇x) = (x◇x)◇((x◇x)◇x).
  --   From h: b◇(a◇q) = a for all b, where q = (c◇d)◇d. Set c=x, d=x: q = (x◇x)◇x.
  --     So b◇(a◇((x◇x)◇x)) = a for all b,a.
  --     Set a = x◇x: b◇((x◇x)◇((x◇x)◇x)) = x◇x. So b◇r = x◇x for all b.
  --     Set a = x◇((x◇x)◇x): b◇((x◇((x◇x)◇x))◇((x◇x)◇x)) = x◇((x◇x)◇x). So b◇(s◇((x◇x)◇x)) = s.
  --   So b◇r = x◇x and b◇(s◇p) = s (where p = (x◇x)◇x) for all b.
  --   If r = s◇p then x◇x = s. And that's what we need!
  --   r = (x◇x)◇p and s◇p = (x◇p)◇p. So need (x◇x)◇p = (x◇p)◇p.
  --   From h: b◇(a◇q) = a. Set a = p = (x◇x)◇x, b = x, c = x, d = x: 
  --     p = x◇(p◇((x◇x)◇x)) = x◇(p◇p). So x◇(p◇p) = p.
  --   From h: b◇(a◇q) = a. Set a = x, b = b, c = x, d = x: b◇(x◇p) = x.
  --     So x◇p is a right-zero for x: b◇(x◇p) = x for all b.
  --   From h: b◇(a◇q) = a. Set a = x◇x, b = b, c = x, d = x: b◇((x◇x)◇p) = x◇x.
  --     So (x◇x)◇p = r is a right-zero for x◇x: b◇r = x◇x.
  --   Now: (x◇x)◇p vs (x◇p)◇p. From h: b◇(a◇p) = a (with c=x,d=x).
  --     Set a = x, b = x: x◇(x◇p) = x. 
  --     Set a = x◇x, b = x: x◇((x◇x)◇p) = x◇x. So x◇r = x◇x.
  --     Set a = x◇p, b = x: x◇((x◇p)◇p) = x◇p. So x◇((x◇p)◇p) = x◇p.
  --   From x◇(x◇p) = x and x◇((x◇p)◇p) = x◇p:
  --     If (x◇p)◇p = x◇p then x◇(x◇p) = x◇p, so x = x◇p. But x◇p is a zero for x (b◇(x◇p)=x).
  --     So x = x◇p. Then from h x b x x: x = b◇(x◇p) = b◇x. So b◇x = x for all b.
  --     Then x◇x = x (set b=x: x◇x = x). And p = (x◇x)◇x = x◇x = x. So p = x.
  --     Then r = (x◇x)◇p = x◇x = x. And s = x◇p = x◇x = x. So s = x = x◇x.
  --     Goal: x = ((x◇x)◇x)◇(x◇x) = (x◇x)◇(x◇x) = x◇x = x. ✓
  --   But we need (x◇p)◇p = x◇p. From h: b◇(a◇p) = a. Set a = (x◇p)◇p... no, set a = x◇p:
  --     b◇((x◇p)◇p) = x◇p. Set b = (x◇p): (x◇p)◇((x◇p)◇p) = x◇p.
  --     And from h (x◇p) b c d: x◇p = b◇((x◇p)◇((c◇d)◇d)). Set c=x, d=x: x◇p = b◇((x◇p)◇p).
  --     So b◇((x◇p)◇p) = x◇p for all b. Set b = p: p◇((x◇p)◇p) = x◇p.
  --     From h p b x x: p = b◇(p◇p). Set b = x◇p: p = (x◇p)◇(p◇p).
  --     So (x◇p)◇(p◇p) = p. And (x◇p)◇((x◇p)◇p) = x◇p.
  --     If p◇p = (x◇p)◇p then p = x◇p. And then from x = b◇(x◇p) = b◇p for all b.
  --     And from h p b x x: p = b◇(p◇p). So b◇(p◇p) = p and b◇p = x. If p◇p = p then x = p.
  --     From h p b x x: p = b◇(p◇p). Set b = p: p = p◇(p◇p). 
  --     From h (p◇p) b x x: p◇p = b◇((p◇p)◇p). Set b = p: p◇p = p◇((p◇p)◇p).
  --     Is p◇p = p? From h p p x x: p = p◇(p◇p). If p◇p = p then p = p◇p. Circular.
  --
  -- I think the approach is:
  -- 1. From h with c=x, d=x: b◇(a◇p) = a for all a,b (where p = (x◇x)◇x).
  -- 2. This means a◇p is a universal right-zero for a.
  -- 3. (x◇p)◇p = x◇p because: from (1) with a = x◇p: b◇((x◇p)◇p) = x◇p for all b.
  --    And from (1) with a = x: b◇(x◇p) = x for all b.
  --    So (x◇p) is a universal right-zero for x, and (x◇p)◇p is a universal right-zero for x◇p.
  --    But is (x◇p)◇p = x◇p? From (1) with a = (x◇p)◇p: b◇(((x◇p)◇p)◇p) = (x◇p)◇p.
  --    From (1) with a = x◇p: b◇((x◇p)◇p) = x◇p. Set b = (x◇p)◇p: ((x◇p)◇p)◇((x◇p)◇p) = x◇p.
  --    Hmm. Not directly (x◇p)◇p = x◇p.
  --    But from h (x◇p) b x x: x◇p = b◇((x◇p)◇p). So b◇((x◇p)◇p) = x◇p for all b.
  --    And from (1) with a = x: b◇(x◇p) = x. So x◇p is a right-zero for x.
  --    And (x◇p)◇p is a right-zero for x◇p.
  --    From h with a = x◇p, b = x, c = x, d = x: x◇p = x◇((x◇p)◇p). ... (*)
  --    From h with a = x, b = x, c = x, d = x: x = x◇(x◇p). ... (**)
  --    From (*): x◇p = x◇((x◇p)◇p). From (**): x = x◇(x◇p).
  --    If (x◇p)◇p = x◇p then x◇p = x◇(x◇p) = x (from (**)). So x◇p = x.
  --    Then from (1): b◇(x) = x for all b (since x◇p = x, and b◇(x◇p) = x).
  --    Wait, b◇(a◇p) = a. Set a = x: b◇(x◇p) = x. If x◇p = x: b◇x = x for all b.
  --    Then x◇x = x (set b=x). p = (x◇x)◇x = x◇x = x. So p = x.
  --    Goal: x = ((x◇x)◇x)◇(x◇x) = p◇(x◇x) = x◇x = x. ✓
  --
  -- So the key step is: (x◇p)◇p = x◇p.
  -- From h (x◇p) b x x: x◇p = b◇((x◇p)◇p) for all b. ... (A)
  -- From h with a = (x◇p)◇p, c = x, d = x: b◇(((x◇p)◇p)◇p) = (x◇p)◇p for all b. ... (B)
  -- From (A) with b = (x◇p)◇p: x◇p = ((x◇p)◇p)◇((x◇p)◇p). ... (C)
  -- From (B) with b = x◇p: (x◇p)◇(((x◇p)◇p)◇p) = (x◇p)◇p. ... (D)
  -- From (A): b◇((x◇p)◇p) = x◇p. From (1) with a = (x◇p)◇p: b◇(((x◇p)◇p)◇p) = (x◇p)◇p.
  --   These are different: (x◇p)◇p vs ((x◇p)◇p)◇p.
  -- From (A) with b = p: p◇((x◇p)◇p) = x◇p. ... (E)
  -- From h p b x x: p = b◇(p◇p). ... (F)
  -- From (F) with b = (x◇p)◇p: p = ((x◇p)◇p)◇(p◇p). ... (G)
  -- From (A) with b = (x◇p): x◇p = (x◇p)◇((x◇p)◇p). ... (H)
  -- From (1) with a = x◇p: b◇((x◇p)◇p) = x◇p (same as A). With b = x◇p: (x◇p)◇((x◇p)◇p) = x◇p (same as H).
  -- From (F) with b = x◇p: p = (x◇p)◇(p◇p). ... (I)
  -- From (I): (x◇p)◇(p◇p) = p. From (H): (x◇p)◇((x◇p)◇p) = x◇p.
  --   If p◇p = (x◇p)◇p then p = x◇p.
  --   From (F) with b = p: p = p◇(p◇p). From (1) with a = p: b◇(p◇p) = p.
  --     Set b = (x◇p): (x◇p)◇(p◇p) = p (same as I).
  --     Set b = p: p◇(p◇p) = p (same as F with b=p).
  --   From (A): b◇((x◇p)◇p) = x◇p for all b. Set b = p: p◇((x◇p)◇p) = x◇p (same as E).
  --   From (F): b◇(p◇p) = p for all b. Set b = p: p◇(p◇p) = p.
  --   If (x◇p)◇p = p◇p then x◇p = p (from (A) and (F): b◇((x◇p)◇p) = x◇p, b◇(p◇p) = p).
  --   So need (x◇p)◇p = p◇p.
  --   From h ((x◇p)◇p) b x x: (x◇p)◇p = b◇(((x◇p)◇p)◇p). ... (J)
  --   From h (p◇p) b x x: p◇p = b◇((p◇p)◇p). ... (K)
  --   If ((x◇p)◇p)◇p = (p◇p)◇p then (x◇p)◇p = p◇p (from (J) and (K)).
  --   And so on, infinite regress.
  --
  -- I think there's a simpler way. Let me just use the fact that from h,
  -- b◇(a◇p) = a for all a,b (where p = (x◇x)◇x, using c=x,d=x).
  -- This means the map a ↦ a◇p is an injection (if a◇p = a'◇p then a = a',
  -- since b◇(a◇p) = a and b◇(a'◇p) = a'). Actually it's a bijection on the 
  -- "right-zero" structure.
  -- More importantly: b◇(a◇p) = a means a = b◇(a◇p). So a = b◇(a◇p) for ALL b.
  -- In particular, a = (a◇p)◇(a◇p) (set b = a◇p). ... (L)
  -- And a = p◇(a◇p) (set b = p). ... (M)
  -- And a = a◇(a◇p) (set b = a). ... (N)
  -- From (N): a = a◇(a◇p). From (L): a = (a◇p)◇(a◇p).
  -- Now set a = x: x = x◇(x◇p) (N) and x = (x◇p)◇(x◇p) (L).
  -- From (L) with a = x: x = (x◇p)◇(x◇p). 
  -- From (N) with a = x: x = x◇(x◇p).
  -- From (L) with a = x◇p: x◇p = ((x◇p)◇p)◇((x◇p)◇p). ... (L')
  -- From (N) with a = x◇p: x◇p = (x◇p)◇((x◇p)◇p). ... (N')
  -- From (A): b◇((x◇p)◇p) = x◇p for all b. From (N'): (x◇p)◇((x◇p)◇p) = x◇p. Consistent (b = x◇p in A).
  -- From (L'): x◇p = ((x◇p)◇p)◇((x◇p)◇p). From (A) with b = (x◇p)◇p: ((x◇p)◇p)◇((x◇p)◇p) = x◇p. Same!
  -- From (M) with a = x: x = p◇(x◇p). From (A) with b = p: p◇((x◇p)◇p) = x◇p.
  -- From (M) with a = p: p = p◇(p◇p). From (F) with b = p: p = p◇(p◇p). Same!
  --
  -- So: x = (x◇p)◇(x◇p) (from L). And goal is x = ((x◇x)◇x)◇(x◇x) = p◇(x◇x).
  -- Need: (x◇p)◇(x◇p) = p◇(x◇x). 
  -- From (A): b◇((x◇p)◇p) = x◇p. Set b = x◇p: (x◇p)◇((x◇p)◇p) = x◇p. (N')
  -- From (N) with a = x: x = x◇(x◇p). So x◇(x◇p) = x.
  -- From (L) with a = x: x = (x◇p)◇(x◇p).
  -- From (N) with a = x◇x: x◇x = (x◇x)◇((x◇x)◇p). So x◇x = (x◇x)◇r where r = (x◇x)◇p.
  --   But from (A) with a = x◇x: b◇((x◇x)◇p) = x◇x. So b◇r = x◇x for all b.
  --   In particular, p◇r = x◇x. And r = (x◇x)◇p. So p◇((x◇x)◇p) = x◇x.
  --   Goal: x = p◇(x◇x). And x◇x = p◇r = p◇((x◇x)◇p). 
  --   So goal is x = p◇(x◇x) = p◇(p◇r) = p◇(p◇((x◇x)◇p)).
  --   From (N) with a = p: p = p◇(p◇p). So p◇(p◇p) = p.
  --   From (M) with a = p: p = p◇(p◇p). Same.
  --   From (F): b◇(p◇p) = p for all b. Set b = p: p◇(p◇p) = p. Same.
  --   So p◇(p◇p) = p. And goal = p◇(x◇x). If x◇x = p◇p then goal = p◇(p◇p) = p. And x = p? 
  --     From (L): x = (x◇p)◇(x◇p). If p = x then x = (x◇x)◇(x◇x). And goal = x◇(x◇x). 
  --     From (N): x = x◇(x◇x). So goal = x. ✓ But we need p = x first.
  --
  -- This is extremely deep. Let me just try the simplest possible Lean proof and iterate.
  -- The key identity: from h with c=x, d=x, we get b◇(a◇p) = a for all a,b where p=(x◇x)◇x.
  -- This means: a = b◇(a◇p) for all b. In particular:
  --   a = a◇(a◇p) (b=a)
  --   a = (a◇p)◇(a◇p) (b=a◇p)  
  --   a = p◇(a◇p) (b=p)
  -- Now, x = (x◇p)◇(x◇p) from b=x◇p.
  -- And x = p◇(x◇p) from b=p.
  -- And x = x◇(x◇p) from b=x.
  -- Goal: x = p◇(x◇x).
  -- x = p◇(x◇p). So need x◇p = x◇x.
  -- x = x◇(x◇p). So x◇(x◇p) = x. 
  -- x◇x = ? From h: x◇x = b◇((x◇x)◇p) for all b. Set b=x: x◇x = x◇((x◇x)◇p). 
  --   Set b=p: x◇x = p◇((x◇x)◇p). Set b=x◇x: x◇x = (x◇x)◇((x◇x)◇p).
  -- If x◇p = x◇x then x = p◇(x◇p) = p◇(x◇x) = goal. ✓
  -- So need: x◇p = x◇x.
  -- From x = x◇(x◇p) (b=x): x◇(x◇p) = x. From x◇x = x◇((x◇x)◇p) (b=x): x◇x = x◇((x◇x)◇p).
  -- If (x◇x)◇p = x◇p then x◇x = x◇(x◇p) = x. So x◇x = x.
  -- Then p = (x◇x)◇x = x◇x = x. So p = x. Then x◇p = x◇x = x. ✓
  -- So need: (x◇x)◇p = x◇p.
  -- From h: b◇(a◇p) = a for all a,b (with c=x,d=x).
  --   Set a = x: b◇(x◇p) = x for all b. So x◇p is a right-zero giving x.
  --   Set a = x◇x: b◇((x◇x)◇p) = x◇x for all b. So (x◇x)◇p is a right-zero giving x◇x.
  --   If (x◇x)◇p = x◇p then x◇x = x (since they're both right-zeros for the same element).
  --   But (x◇x)◇p = x◇p means (x◇x)◇p = x◇p. From (A) with a = x: b◇(x◇p) = x.
  --     Set b = x◇x: (x◇x)◇(x◇p) = x. 
  --   From (A) with a = x: b◇(x◇p) = x. Set b = x: x◇(x◇p) = x.
  --   So x◇(x◇p) = x and (x◇x)◇(x◇p) = x. Both equal x.
  --   Now, from h: a = b◇(a◇p). Set a = x◇x, b = x: x◇x = x◇((x◇x)◇p).
  --     Set a = x, b = x: x = x◇(x◇p). So x◇(x◇p) = x.
  --     If (x◇x)◇p = x◇p, then x◇x = x◇(x◇p) = x. But (x◇x)◇p = x◇p is what we're trying to prove!
  --
  -- OK, I think the issue is that the proof requires showing (x◇x)◇p = x◇p, which
  -- follows from the fact that both are right-zeros, but they give different results
  -- (x vs x◇x), so they're equal iff x = x◇x, which is circular.
  --
  -- Let me try a COMPLETELY different approach. Maybe I don't need singleton.
  -- Maybe I can prove the goal directly.
  -- Goal: x = ((x◇x)◇x) ◇ (x◇x) = p ◇ (x◇x).
  -- From h: a = b ◇ (a ◇ ((c◇d)◇d)).
  --   Set a = x, b = p, c = x, d = x: x = p ◇ (x ◇ p). So x = p◇(x◇p).
  --   So goal x = p◇(x◇x) becomes p◇(x◇p) = p◇(x◇x). Need x◇p = x◇x.
  --   Set a = x, b = x, c = x, d = x: x = x ◇ (x ◇ p). So x◇(x◇p) = x.
  --   Set a = x◇x, b = x, c = x, d = x: x◇x = x ◇ ((x◇x) ◇ p). So x◇((x◇x)◇p) = x◇x.
  --   From x◇(x◇p) = x and x◇((x◇x)◇p) = x◇x:
  --     If x◇p = (x◇x)◇p then x = x◇x. But this is circular.
  --   From a = (a◇p)◇(a◇p) (setting b = a◇p):
  --     x = (x◇p)◇(x◇p). 
  --     x◇x = ((x◇x)◇p)◇((x◇x)◇p).
  --   From a = p◇(a◇p) (setting b = p):
  --     x = p◇(x◇p). Goal: x = p◇(x◇x). So need x◇p = x◇x. STILL circular.
  --
  -- Hmm. Let me try yet another substitution in h.
  -- h x y z w : x = y ◇ (x ◇ ((z◇w)◇w))
  -- Set z = x◇x, w = x: (z◇w)◇w = ((x◇x)◇x)◇x = p◇x.
  --   x = y ◇ (x ◇ (p◇x)). So y◇(x◇(p◇x)) = x for all y.
  -- Set z = x, w = x◇x: (z◇w)◇w = (x◇(x◇x))◇(x◇x).
  --   x = y ◇ (x ◇ ((x◇(x◇x))◇(x◇x))). For all y.
  -- 
  -- Actually, the key insight might be that the RHS of h is independent of y, z, w
  -- (it always equals x). So for any element e of the form x◇((z◇w)◇w), we have
  -- y◇e = x for all y. The set of such elements for varying z,w is:
  --   { x◇((z◇w)◇w) : z,w ∈ G }
  -- For any such e, y◇e = x for all y. In particular e◇e = x.
  --
  -- Now: p = (x◇x)◇x. Is p of the form x◇((z◇w)◇w)?
  -- p = (x◇x)◇x. For this to be x◇((z◇w)◇w), need x = x (ok) and (z◇w)◇w = ... 
  -- wait, p = (x◇x)◇x, and x◇((z◇w)◇w) has x on the left. So need (x◇x) = x and 
  -- ((z◇w)◇w) = x. Or (x◇x) = x◇something. Hmm, not directly.
  --
  -- But: x◇p = x◇((x◇x)◇x). Is this of the form x◇((z◇w)◇w)?
  -- x◇((x◇x)◇x): set z = x, w = x: (z◇w)◇w = (x◇x)◇x = p. So x◇p = x◇((x◇x)◇x) = x◇((z◇w)◇w) with z=x,w=x.
  -- YES! So x◇p is of the form x◇((z◇w)◇w), and therefore y◇(x◇p) = x for all y. ✓ (This is just h with c=x,d=x.)
  --
  -- Now: x◇x. Is x◇x of the form x◇((z◇w)◇w)? 
  -- x◇x = x◇((z◇w)◇w) iff (z◇w)◇w = x. Can we find z,w such that (z◇w)◇w = x?
  -- From h: x = y◇(x◇((z◇w)◇w)). Set y = x, z = x, w = x: x = x◇(x◇p). So x◇(x◇p) = x.
  -- Hmm, that gives x = x◇(x◇p), not (z◇w)◇w = x.
  -- From a = (a◇p)◇(a◇p): set a = x: x = (x◇p)◇(x◇p). 
  -- From a = b◇(a◇p): set a = x, b = x◇p: x = (x◇p)◇(x◇p). Same.
  -- Is x of the form (z◇w)◇w? Set z = x◇p, w = x◇p: ((x◇p)◇(x◇p))◇(x◇p) = x◇(x◇p) = x. 
  -- Wait: (z◇w)◇w with z = x◇p, w = x◇p: ((x◇p)◇(x◇p))◇(x◇p). And (x◇p)◇(x◇p) = x (from above).
  -- So x◇(x◇p). And x◇(x◇p) = x (from h x x x x). So (z◇w)◇w = x with z = w = x◇p. ✓
  -- So x IS of the form (z◇w)◇w (with z = w = x◇p).
  -- Therefore x◇x = x◇((z◇w)◇w) with z = w = x◇p. 
  -- So y◇(x◇x) = x for all y! (Because x◇x is of the form x◇((z◇w)◇w).)
  -- In particular: p◇(x◇x) = x. THAT'S THE GOAL! ✓✓✓
  --
  -- So the proof is:
  -- 1. From h x y x x: x = y◇(x◇p) for all y, where p = (x◇x)◇x. (Setting c=x, d=x.)
  -- 2. From (1) with y = x◇p: x = (x◇p)◇(x◇p). ... (A)
  -- 3. From (1) with y = x: x = x◇(x◇p). ... (B) 
  -- 4. (z◇w)◇w with z = w = x◇p: ((x◇p)◇(x◇p))◇(x◇p) = x◇(x◇p) [using (A)] = x [using (B)].
  -- 5. So x = (z◇w)◇w with z = w = x◇p.
  -- 6. Therefore x◇x = x◇((z◇w)◇w), and from h: y◇(x◇((z◇w)◇w)) = x for all y.
  -- 7. So y◇(x◇x) = x for all y. In particular p◇(x◇x) = x.
  -- 8. Goal: x = p◇(x◇x) = ((x◇x)◇x)◇(x◇x). ✓
  --
  -- This is the proof! Let me write it in Lean.
"""),
    },
}


def main():
    for pid, entry in PROOFS.items():
        print(f"\n{'='*60}")
        print(f"=== {pid} ===")
        print(f"{'='*60}")
        result = test_proof(pid, entry["verdict"], entry["code"])
        print(f"Status: {result['status']}")
        print(f"Error: {result.get('error_code')}")
        msg = result.get("message", "")
        if msg:
            print(f"Message: {msg[:1500]}")


if __name__ == "__main__":
    main()