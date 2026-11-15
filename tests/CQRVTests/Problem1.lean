module

import CQRV.Synthesis.Problem1
meta import CQRV.Synthesis.Problem1

/-!
# Tests for `CQRV.Synthesis.Problem1` (Stage 23c; PHASE2_SPEC §B.2; report §6.1.4)

The axiom lines of `problem1_T_lower_bound` and `planB_valid`; the bound at n = 8 is 40 and
candidate B's plan costs 40 there; a schedule by hand that reaches the bound at n = 4 (which
candidate B does not: it costs 12 there); a schedule with three clean indices that does better
(`8n − 28`), showing that the number of clean ancillae is what the bound counts.
-/

namespace CQRV.Tests.Problem1

open CQRV CQRV.Synthesis CQRV.Synthesis.Problem1

/-- info: 'CQRV.Synthesis.Problem1.problem1_T_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms problem1_T_lower_bound

/-- info: 'CQRV.Synthesis.Problem1.planB_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms planB_valid

/-! ## The bound at n = 8 -/

#guard 8 * 8 - 24 == 40

example : cost (initB 8) (planB 8) = 40 := planB_cost 8 (by decide)

example : 40 ≤ cost (initB 8) (planB 8) := planB_bound 8 (by decide)

example : (mczFew 8 .logDepth).toOption.map Circuit.tCount = some 40 := by
  rw [planB_tCount 8 (by decide), planB_cost 8 (by decide)]

/-! ## A schedule by hand that reaches the bound at n = 4 -/

/-- Four live values at `1 … 4`, two fresh clean indices `0` and `5`. -/
def init4 : P1State 6 := ⟨fun i => decide (i.val = 0 ∨ i.val = 5), fun i => decide (i.val = 0 ∨ i.val = 5)⟩

/-- `(0; 1, 2)` then `(5; 3, 4)`: two ANDs, 8 T = 8 · 4 − 24. -/
def hand4 : List (P1Op 6) := [(0, 1, 2), (5, 3, 4)]

#guard valid init4 hand4
#guard cost init4 hand4 == 8
#guard (run init4 hand4).live == 2

example : 8 * 4 - 24 ≤ cost init4 hand4 :=
  problem1_T_lower_bound (s := init4) (os := hand4) (by decide) (by decide) (by decide) (by decide)
    (le_refl 4)

/-- Candidate B does not reach the bound at n = 4: its plan costs 12. -/
example : cost (initB 4) (planB 4) = 12 := planB_cost_small 4 (by decide)

/-! ## Three clean indices do better: `8n − 28` -/

/-- Five live values at `1 … 5`, three fresh clean indices `0`, `6`, `7`. -/
def init5 : P1State 8 :=
  ⟨fun i => decide (i.val = 0 ∨ i.val = 6 ∨ i.val = 7), fun i => decide (i.val = 0 ∨ i.val = 6 ∨ i.val = 7)⟩

/-- Three ANDs: `(0; 1, 2)`, `(6; 3, 4)`, `(7; 0, 5)` — 12 T = 8 · 5 − 28, below the two-ancilla
bound 8 · 5 − 24 = 16. -/
def hand5 : List (P1Op 8) := [(0, 1, 2), (6, 3, 4), (7, 0, 5)]

#guard valid init5 hand5
#guard cost init5 hand5 == 12
#guard (run init5 hand5).live == 2
#guard init5.freshCard == 3

/-- The general form at `|fresh₀| = 3`, `n = 5`, `k = 2`: `8 · 3 − 4 · 3 = 12`, attained. -/
example : 8 * (init5.live - (run init5 hand5).live) -
    4 * min init5.freshCard (init5.live - (run init5 hand5).live) ≤ cost init5 hand5 :=
  cost_lower_bound (by decide)

example : cost init5 hand5 = 8 * 5 - 28 := by decide

/-! ## The model's laws on the plan -/

/-- `live_run` on candidate B at n = 8: six steps from eight live values to two. -/
example : (run (initB 8) (planB 8)).live + (planB 8).length = (initB 8).live :=
  live_run (planB_valid 8 (by decide))

end CQRV.Tests.Problem1
