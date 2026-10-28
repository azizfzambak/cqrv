module

import CQRV.Realizability.Composition
import CQRV.Realizability.Coherent
import CQRV.Realizability.Obstruction
import Mathlib.Topology.Instances.Nat

/-!
# Tests for `CQRV.Realizability` (report §2.1.1–2.1.2)

`Spec.dom` and `Spec.comp` on a small `Fin` example, and one use of `Spec.relax_zero`; the
§2.3.3 three-stage pipeline as two applications of Theorem 3.3a (Stage 10a); Theorem 3.3b
instantiated with `distD := fun _ _ => 2` as a non-vacuity check of its hypotheses (Stage 10b);
the diamond distance and `coherent_composition_diamond` (Stage 13b).
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

/-! ## §2.3.3 — the three-stage pipeline composes (Theorem 3.3a twice, ε = 0)

Abstract stages with the report's numbers: δ = 0.01, 0.005, 0.002 and grades
(10, 50, 100, 5), (12, 200, 800, 8), (8, 30, 0, 0). Stage 1 checks the grade arithmetic
(`tests/CQRVTests/Grades.lean`); here the point is that `measured_composition` composes. -/
example {X₁ X₂ X₃ X₄ d₂ d₃ d₄ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype X₂]
    [DecidableEq X₂] [Fintype X₃] [DecidableEq X₃] [Fintype X₄] [DecidableEq X₄] [Fintype d₂]
    [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃] [Fintype d₄] [DecidableEq d₄]
    [MetricSpace X₂] [MetricSpace X₃] [MetricSpace X₄]
    {S₁ : Spec X₁ X₂} {S₂ : Spec X₂ X₃} {S₃ : Spec X₃ X₄}
    {dec₁ : POVM X₂ d₂} {dec₂ : POVM X₃ d₃} {dec₃ : POVM X₄ d₄}
    {Φ₁ : GradedChannel X₁ d₂} {Φ₂ : GradedChannel X₂ d₃} {Φ₃ : GradedChannel X₃ d₄}
    (h₁ : Realizes S₁ dec₁ Φ₁ 0 0.01 ⟨10, 50, 100, 5⟩)
    (h₂ : Realizes S₂ dec₂ Φ₂ 0 0.005 ⟨12, 200, 800, 8⟩)
    (h₃ : Realizes S₃ dec₃ Φ₃ 0 0.002 ⟨8, 30, 0, 0⟩)
    (hdom₁₂ : ∀ x ∈ S₁.dom, ∀ y, S₁.relax 0 x y → y ∈ S₂.dom)
    (hdom₂₃ : ∀ x ∈ (S₂.comp S₁).dom, ∀ y, (S₂.comp S₁).relax 0 x y → y ∈ S₃.dom)
    (hne₂ : ∀ y ∈ S₂.dom, ∀ y' z', S₂ y' z' → ∃ z, S₂ y z ∧ dist z z' ≤ dist y y')
    (hne₃ : ∀ y ∈ S₃.dom, ∀ y' z', S₃ y' z' → ∃ z, S₃ y z ∧ dist z z' ≤ dist y y') :
    Realizes (S₃.comp (S₂.comp S₁)) dec₃ (measuredComp (measuredComp Φ₁ dec₁ Φ₂) dec₂ Φ₃)
      0 0.017 ⟨12, 280, 900, 8⟩ := by
  have h₁₂ := measured_composition h₁ h₂ hdom₁₂ hne₂ (by norm_num) (by norm_num) (by norm_num)
  rw [add_zero] at h₁₂
  have h := measured_composition h₁₂ h₃ hdom₂₃ hne₃ (by norm_num) (by norm_num) (by norm_num)
  rwa [add_zero, show ((0.01 : ℝ) + 0.005) + 0.002 = 0.017 by norm_num,
    show ((⟨10, 50, 100, 5⟩ : Grade) + ⟨12, 200, 800, 8⟩) + ⟨8, 30, 0, 0⟩ = ⟨12, 280, 900, 8⟩
      by decide] at h

/-! ## Axiom audit (CLAUDE.md rule 10) — Theorem 3.3a (exact stages), Theorem 3.1 -/

#print axioms measured_composition_exact
#print axioms no_cloning_obstruction

/-! ## Axiom audit — Theorem 3.3a, general ε (Stage 10a) -/

/-- info: 'CQRV.relax_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms relax_comp

/-- info: 'CQRV.measured_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms measured_composition

/--
info: 'CQRV.measured_composition_exact'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms measured_composition_exact'

/-! ## Theorem 3.3b (Stage 10b) -/

/-- Report §2.3.2 — non-vacuity of the hypotheses of `coherent_composition`: the constant
distance `2` satisfies `hdistD` (`TrDistance ≤ 1`), so the theorem instantiates for any ideal
realization and any implemented channels, with `η_f = η_g = 2` (δ grows by 2). -/
example {X Y Z dY dZ : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z] [MetricSpace Z] [Fintype dY] [DecidableEq dY] [Fintype dZ]
    [DecidableEq dZ] {S_f : Spec X Y} {S_g : Spec Y Z} {dec : POVM Z dZ}
    {Φ₁ : CPTPMap X dY} {Ψ₁ : CPTPMap dY dZ} {Φ₂ : GradedChannel X dY}
    {Ψ₂ : GradedChannel dY dZ} {ε₀ δ₀ : ℝ}
    (hideal : Realizes (S_g.comp S_f) dec ⟨Ψ₁ ∘ₘ Φ₁, 0⟩ ε₀ δ₀ 0) :
    Realizes (S_g.comp S_f) dec ⟨Ψ₂.chan ∘ₘ Φ₂.chan, Φ₂.grade + Ψ₂.grade⟩ ε₀ (δ₀ + (2 + 2) / 2)
      (Φ₂.grade + Ψ₂.grade) :=
  coherent_composition (fun _ _ => 2)
    (fun ρ σ τ => by linarith [trDistance_le_one (ρ τ) (σ τ)])
    hideal le_rfl le_rfl le_rfl le_rfl

/-! ## Axiom audit — trace-distance facts and Theorem 3.3b (Stage 10b) -/

/-- info: 'CQRV.trDistance_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trDistance_triangle

/-- info: 'CQRV.trDistance_cptp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trDistance_cptp_le

/--
info: 'CQRV.prob_sub_le_trDistance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prob_sub_le_trDistance

/--
info: 'CQRV.coherent_composition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms coherent_composition

/-! Stage 13b: the diamond distance on a qubit, the domination lemma, Theorem 3.3b with `‖·‖⋄`. -/

example (Λ : CPTPMap (Fin 2) (Fin 2)) : diamondDist Λ Λ = 0 := diamondDist_self Λ

example (Λ₁ Λ₂ : CPTPMap (Fin 2) (Fin 2)) (ρ : MState (Fin 2)) :
    TrDistance (Λ₁ ρ) (Λ₂ ρ) ≤ 1 := by
  have h₁ := diamond_dominates Λ₁ Λ₂ ρ
  have h₂ := diamondDist_le_two Λ₁ Λ₂
  linarith

/--
info: 'CQRV.diamondDist_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diamondDist_bddAbove

/--
info: 'CQRV.diamondDist_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diamondDist_nonneg

/--
info: 'CQRV.diamondDist_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diamondDist_le_two

/--
info: 'CQRV.diamondDist_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diamondDist_self

/--
info: 'CQRV.diamondDist_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diamondDist_comm

/--
info: 'CQRV.diamondDist_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diamondDist_triangle

/--
info: 'CQRV.traceRight_prod_id_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms traceRight_prod_id_apply

/--
info: 'CQRV.diamond_dominates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diamond_dominates

/--
info: 'CQRV.prod_id_compose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prod_id_compose

/--
info: 'CQRV.diamondDist_compose_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diamondDist_compose_le

/--
info: 'CQRV.coherent_composition_diamond' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms coherent_composition_diamond

end CQRV.Tests.Realizability
