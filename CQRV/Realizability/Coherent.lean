module

public import CQRV.Realizability.TraceDistance

/-!
# CQRV.Realizability.Coherent

Report §2.3.2 — Theorem 3.3b (coherent-interface composition), proved in Stage 10b.

Neither Mathlib nor Physlib has the diamond norm, so the channel distance is an explicit
parameter `dist⋄` that dominates twice the trace distance on every input (docs/DECISIONS.md,
2026-10-23). The proof uses only the trace-distance facts of `TraceDistance`; instantiating
`dist⋄` with the real diamond norm needs only the domination lemma `‖Λ₁ρ − Λ₂ρ‖₁ ≤ ‖Λ₁ − Λ₂‖⋄`,
a remaining Phase III item (§9.3; docs/DECISIONS.md, 2026-10-25).
-/

@[expose] public section

noncomputable section

namespace CQRV

variable {X Y Z dY dZ : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z] [Fintype dY] [DecidableEq dY] [Fintype dZ] [DecidableEq dZ]

set_option linter.unusedSectionVars false in
/-- Report §2.3.2, Theorem 3.3b and "Reading of the four channels".

`Φ₁`, `Ψ₁` are the ideal channels whose composite `Ψ₁ ∘ Φ₁` (ε₀,δ₀)-realizes `g ∘ f` (they carry
no grade: grade 0 against budget 0); `Φ₂`, `Ψ₂` are the implemented graded channels with
`dist⋄ Φ₂ Φ₁ ≤ η_f` and `dist⋄ Ψ₂ Ψ₁ ≤ η_g`. Then `Ψ₂ ∘ Φ₂` (ε₀, δ₀ + ½(η_f + η_g))-realizes
`g ∘ f` within `r ⊕ s`.

`dist⋄` stands for the diamond norm `‖Λ₁ − Λ₂‖⋄`; its only assumed property is
`2 · TrDistance (Λ₁ ρ) (Λ₂ ρ) ≤ dist⋄ Λ₁ Λ₂` on every input `ρ` (`TrDistance` is ½‖·‖₁, so this
is `‖Λ₁ ρ − Λ₂ ρ‖₁ ≤ ‖Λ₁ − Λ₂‖⋄`), which matches the report's ½ in `δ₀ + ½(η_f + η_g)`.
It is a family over channel types because `Φ` and `Ψ` have different input/output spaces.

Proof (Stage 10b): for `ρ = encode x`, the triangle inequality, data processing for `Ψ₂` and
`hdistD` twice give `TrDistance (Ψ₁Φ₁ρ) (Ψ₂Φ₂ρ) ≤ (η_f + η_g)/2`, and the measurement bound
`prob_sub_le_trDistance_of` moves the success probability by at most that much. -/
theorem coherent_composition
    (distD : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B],
      CPTPMap A B → CPTPMap A B → ℝ)
    (hdistD : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
      (Λ₁ Λ₂ : CPTPMap A B) (ρ : MState A), 2 * TrDistance (Λ₁ ρ) (Λ₂ ρ) ≤ distD Λ₁ Λ₂)
    [MetricSpace Z] {S_f : Spec X Y} {S_g : Spec Y Z} {dec : POVM Z dZ}
    {Φ₁ : CPTPMap X dY} {Ψ₁ : CPTPMap dY dZ} {Φ₂ : GradedChannel X dY}
    {Ψ₂ : GradedChannel dY dZ} {ε₀ δ₀ η_f η_g : ℝ} {r s : Grade}
    (hideal : Realizes (S_g.comp S_f) dec ⟨Ψ₁ ∘ₘ Φ₁, 0⟩ ε₀ δ₀ 0)
    (hΦ : distD Φ₂.chan Φ₁ ≤ η_f) (hΨ : distD Ψ₂.chan Ψ₁ ≤ η_g)
    (hr : Φ₂.grade ≤ r) (hs : Ψ₂.grade ≤ s) :
    Realizes (S_g.comp S_f) dec ⟨Ψ₂.chan ∘ₘ Φ₂.chan, Φ₂.grade + Ψ₂.grade⟩ ε₀
      (δ₀ + (η_f + η_g) / 2) (r + s) := by
  refine ⟨Grade.seqComp_mono hr hs, fun x hx => ?_⟩
  have hid := hideal.2 x hx
  simp only [CPTPMap.compose_eq] at hid ⊢
  set ρ := encode x
  -- `TrD(Ψ₁Φ₁ρ, Ψ₂Φ₂ρ) ≤ TrD(Ψ₁Φ₁ρ, Ψ₂Φ₁ρ) + TrD(Ψ₂Φ₁ρ, Ψ₂Φ₂ρ) ≤ η_g/2 + TrD(Φ₁ρ, Φ₂ρ)`
  have htri := trDistance_triangle (Ψ₁ (Φ₁ ρ)) (Ψ₂.chan (Φ₁ ρ)) (Ψ₂.chan (Φ₂.chan ρ))
  have hdp := trDistance_cptp_le Ψ₂.chan (Φ₁ ρ) (Φ₂.chan ρ)
  have hg := hdistD Ψ₂.chan Ψ₁ (Φ₁ ρ)
  have hf := hdistD Φ₂.chan Φ₁ ρ
  rw [trDistance_symm] at hg hf
  have hm := prob_sub_le_trDistance_of dec (Ψ₁ (Φ₁ ρ)) (Ψ₂.chan (Φ₂.chan ρ))
    ((S_g.comp S_f).relax ε₀ x)
  linarith

end CQRV

end

end
