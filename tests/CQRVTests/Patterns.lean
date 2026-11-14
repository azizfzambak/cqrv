module

import Lean
import CQRV.Patterns.Sound
meta import Lean
meta import CQRV.Patterns.Sound

/-!
# Tests for `CQRV.Patterns` (Stage 21a3; report §3.2, Definition 4.1; PHASE2_SPEC §A.5 (6), (6′))

The syntactic record projects to the matching library; every name it carries exists in the
environment; the two semantic instances `groverSem` and `countSem` are sorry-free (the standard
three axioms); `countSem.proof` applies at the AND network `n4` of the Stage 19c tests.
-/

namespace CQRV.Tests.Patterns

open CQRV CQRV.Patterns CQRV.Matching CQRV.Synthesis CQRV.Grover CQRV.Counting

/-! ## F1 — the syntactic record -/

example : qplpLibrary.map (·.entry) = library := qplpLibrary_entries
#guard qplpLibrary.map (·.entry.name) == ["Grover", "Count"]
#guard qplpLibrary.map (·.gradeKind.name) == ["measured", "composed_bound"]
#guard (QPLP.ofEntry groverEntry).map (·.builder) == some .grover
#guard (QPLP.ofEntry countEntry).map (·.builder) == some .count
#guard (QPLP.ofEntry { groverEntry with name := "Other" }).isNone

-- Every `specName`, `lemmaName` and `semName` of `qplpLibrary` is a constant of the
-- environment (a missing one fails the build).
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  for q in qplpLibrary do
    for nm in [q.specName, q.lemmaName, q.semName] do
      unless env.contains nm do
        throwError "QPLP {q.entry.name}: the name `{nm}` is not in the environment"
  logInfo m!"qplpLibrary: {qplpLibrary.length} records, every specName / lemmaName / semName found"

/-! ## F2 — the semantic instances are sorry-free -/

/-- info: 'CQRV.Patterns.groverSem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms groverSem

/-- info: 'CQRV.Patterns.countSem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms countSem

/-- The discrete metric: distance 0 on the diagonal, 1 off it. -/
example (x y : DiscreteOut (Reg 3)) (h : x ≠ y) : dist x y = 1 := by
  simp [DiscreteOut.dist_eq, h]

/-- `x₀ ∧ x₁ ∧ x₂ ∧ x₃` on four inputs (`M = 1`): the network `n4` of the Stage 19c tests
(`tests/CQRVTests/Counting.lean`; test modules export nothing, so the literal is repeated). -/
def n4 : Network :=
  ⟨4, #[.input 0, .input 1, .input 2, .input 3, .and 0 1, .and 4 2, .and 5 3], [6]⟩

/-- The counting circuit of `n4` at `m = 2` (as `cc` of the Stage 19c tests). -/
def cc : Circuit := (countingCircuit n4 4 2).toOption.getD default

#guard (countingCircuit n4 4 2).toBool && cc.nData == 6

/-- `countSem.proof` at the AND network `n4` of the Stage 19c tests (`x₀ ∧ x₁ ∧ x₂ ∧ x₃`, `M = 1`),
`m = 2`, shape tree, mode MBU: realization of `CountSpec 2 (1/2^4)` under `countPOVM 4 2 (1/2^4)`
within the measured grade, and restoration with `U_count`. -/
example (hcard : (Finset.univ.filter fun x => Network.pred n4 4 x = true).card = 1)
    (hC : countingCircuit n4 4 2 none .tree .mbu = .ok cc) :
    Realizes (CountSpec 2 ((1 : ℕ) / 2 ^ 4 : ℝ)) (countPOVM 4 2 ((1 : ℕ) / 2 ^ 4 : ℝ))
        (groverChannel (4 + 2) cc) (ae_eps ((1 : ℕ) / 2 ^ 4 : ℝ) 2) ae_delta
        (Synthesis.grade cc) ∧
      AncRestore (4 + 2) cc.nAnc cc (U_count (Network.pred n4 4) 2 none) :=
  countSem.proof ⟨4, 1, 2, n4, Network.pred n4 4, hcard, by decide, rfl, rfl, rfl,
    .tree, .mbu⟩ ⟨Nat.le_succ 1, Nat.le_refl 1⟩ cc hC

/-- The composed-bound corollary at the same instance: any grade above the measured one. -/
example (hcard : (Finset.univ.filter fun x => Network.pred n4 4 x = true).card = 1)
    (hC : countingCircuit n4 4 2 none .tree .mbu = .ok cc) (g : Grade)
    (hg : Synthesis.grade cc ≤ g) :
    Realizes (CountSpec 2 ((1 : ℕ) / 2 ^ 4 : ℝ)) (countPOVM 4 2 ((1 : ℕ) / 2 ^ 4 : ℝ))
      (groverChannel (4 + 2) cc) (ae_eps ((1 : ℕ) / 2 ^ 4 : ℝ) 2) ae_delta g :=
  countSem.realizes_of_le ⟨4, 1, 2, n4, Network.pred n4 4, hcard, by decide, rfl,
    rfl, rfl, .tree, .mbu⟩ ⟨Nat.le_succ 1, Nat.le_refl 1⟩ cc hC g hg

end CQRV.Tests.Patterns
