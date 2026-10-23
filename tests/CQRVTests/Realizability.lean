module

import CQRV.Realizability.Composition
import CQRV.Realizability.Obstruction
import Mathlib.Topology.Instances.Nat

/-!
# Tests for `CQRV.Realizability` (report §2.1.1–2.1.2)

`Spec.dom` and `Spec.comp` on a small `Fin` example, and one use of `Spec.relax_zero`.
No numeric test of `Realizes` yet (Stage 2 task).
-/

namespace CQRV.Tests.Realizability

open CQRV

/-- Successor on `{0, 1}`, undefined at `2`. -/
abbrev Sf : Spec (Fin 3) (Fin 3) := fun x y => x.val < 2 ∧ y.val = x.val + 1
/-- Identity relation. -/
abbrev Sg : Spec (Fin 3) (Fin 3) := fun y z => z = y

example : (0 : Fin 3) ∈ Sf.dom := by unfold Spec.dom; decide
example : (2 : Fin 3) ∉ Sf.dom := by unfold Spec.dom; decide
example : Spec.comp Sg Sf 1 2 := by unfold Spec.comp; decide
example : ¬ Spec.comp Sg Sf 1 1 := by unfold Spec.comp; decide
example : (2 : Fin 3) ∉ (Spec.comp Sg Sf).dom := by unfold Spec.dom Spec.comp; decide

/-- `Fin n` has no `MetricSpace` instance in the pinned Mathlib, so `relax_zero` is exercised on
an `ℕ`-valued specification. -/
abbrev Sn : Spec (Fin 3) ℕ := fun x y => y = x.val + 1

example : Sn.relax 0 0 1 := by rw [Spec.relax_zero]; rfl

/-! ## `RealizesExact` needs no metric

`Fin 4` has no `MetricSpace` instance, yet the discrete-case predicate typechecks (the Grover
output type is `Fin (2^n)`, Stage 7). -/
example (S : Spec (Fin 2) (Fin 4)) (dec : POVM (Fin 4) (Fin 4))
    (Φ : GradedChannel (Fin 2) (Fin 4)) (δ : ℝ) (r : Grade) : Prop :=
  RealizesExact S dec Φ δ r

/-! ## Axiom audit (CLAUDE.md rule 10) — Theorem 3.3a (exact stages), Theorem 3.1 -/

#print axioms measured_composition_exact
#print axioms no_cloning_obstruction

end CQRV.Tests.Realizability
