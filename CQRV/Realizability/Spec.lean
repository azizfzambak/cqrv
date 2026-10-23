module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Defs

/-!
# CQRV.Realizability.Spec

Report §2.1.1 (Definition 2.1) — classical specifications as relations `S ⊆ X × Y`, their
domain, relational composition, and the ε-relaxation used by (ε,δ)-realization (§2.1.2).
-/

@[expose] public section

namespace CQRV

/-- Report §2.1.1, Definition 2.1 — a classical specification is a relation `S ⊆ X × Y`:
`S x y` means "on input `x`, output `y` is acceptable". -/
def Spec (X Y : Type) := X → Y → Prop

namespace Spec

variable {X Y Z : Type}

/-- Report §2.1.1, Definition 2.1 — the domain of `S`: inputs with at least one acceptable
output. Realization (Definition 2.2) only constrains inputs in the domain. -/
def dom (S : Spec X Y) : Set X := {x | ∃ y, S x y}

/-- Report §2.1.1, §2.3.2 — relational composition `g ∘ f`: `z` is acceptable for `x` when
some intermediate `y` is acceptable for `x` under `f` and `z` is acceptable for `y` under `g`. -/
def comp (g : Spec Y Z) (f : Spec X Y) : Spec X Z := fun x z => ∃ y, f x y ∧ g y z

/-- Report §2.1.2 — the ε-relaxation `S^ε`: `y` is acceptable for `x` when it lies within
distance `ε` of some `S`-acceptable output. The output metric is a type parameter
(docs/DECISIONS.md, 2026-10-21); the MVP uses only `ε = 0`. -/
def relax [PseudoMetricSpace Y] (S : Spec X Y) (ε : ℝ) : Spec X Y :=
  fun x y => ∃ y', S x y' ∧ dist y y' ≤ ε

/-- Report §2.1.2 — on a metric space (distinct points at positive distance), `S^0 = S`. -/
theorem relax_zero [MetricSpace Y] (S : Spec X Y) : S.relax 0 = S := by
  funext x y
  apply propext
  constructor
  · rintro ⟨y', hS, hd⟩
    rwa [dist_le_zero.mp hd]
  · intro h
    exact ⟨y, h, by rw [dist_self]⟩

end Spec

end CQRV

end
