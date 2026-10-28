module

public import CQRV.Realizability.TraceDistance

/-!
# CQRV.Realizability.Diamond

Report §2.3.2 (Theorem 3.3b, `dist⋄`), §9.3 (Phase III) — Stage 13b: the diamond distance of two
channels and the domination lemma `‖Λ₁ρ − Λ₂ρ‖₁ ≤ ‖Λ₁ − Λ₂‖⋄`.

Physlib (pinned commit 96a6bc5) has no diamond norm or completely bounded trace norm; it has the
tensor product of channels (`CPTPMap.prod`, `⊗ᶜᵖ`), the identity channel (`CPTPMap.id`), the
partial trace as a channel (`CPTPMap.traceRight`) and product states (`⊗ᴹ`), which is all the
definition and the domination lemma use (docs/DECISIONS.md, 2026-10-28, Stage 13b).
-/

@[expose] public section

noncomputable section

namespace CQRV

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Report §2.3.2, `dist⋄` (Stage 13b decision 1) — the diamond distance `‖Λ₁ − Λ₂‖⋄`, as the
stabilized trace-norm distance with a reference system of the input's dimension, restricted to
density operators:
`diamondDist Λ₁ Λ₂ = ⨆ ρ : MState (A × A), 2 · TrDistance ((Λ₁ ⊗ id) ρ) ((Λ₂ ⊗ id) ρ)`
(`TrDistance` is ½‖·‖₁). This form is the diamond norm of the difference of two channels by
Watrous, *The Theory of Quantum Information* (2018), §3.3: a reference system of the input's
dimension suffices, and for a difference of channels the supremum over density operators on
`A ⊗ A` attains it. The equivalence with the operator-norm definition is not proved here. -/
def diamondDist (Λ₁ Λ₂ : CPTPMap A B) : ℝ :=
  ⨆ ρ : MState (A × A), 2 * TrDistance ((Λ₁ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ) ((Λ₂ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ)

/-- Report §2.3.2 — `TrDistance ρ ρ = 0`. -/
theorem trDistance_self {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) :
    TrDistance ρ ρ = 0 := by
  simp [TrDistance]

/-- Report §2.3.2 — `0 ≤ TrDistance ρ σ`. -/
theorem trDistance_nonneg {d : Type} [Fintype d] [DecidableEq d] (ρ σ : MState d) :
    0 ≤ TrDistance ρ σ := by
  have h := trDistance_triangle ρ σ ρ
  rw [trDistance_self, trDistance_symm σ ρ] at h
  linarith

/-- Report §2.3.2 (Stage 13b decision 2) — the range of the supremum is bounded by `2`
(`trDistance_le_one`), so `diamondDist` is a genuine `ciSup`. -/
theorem diamondDist_bddAbove (Λ₁ Λ₂ : CPTPMap A B) :
    BddAbove (Set.range fun ρ : MState (A × A) =>
      2 * TrDistance ((Λ₁ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ) ((Λ₂ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ)) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨ρ, rfl⟩
  have := trDistance_le_one ((Λ₁ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ) ((Λ₂ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ)
  linarith

/-- Report §2.3.2 (Stage 13b decision 2) — `0 ≤ diamondDist Λ₁ Λ₂`. -/
theorem diamondDist_nonneg (Λ₁ Λ₂ : CPTPMap A B) : 0 ≤ diamondDist Λ₁ Λ₂ :=
  Real.iSup_nonneg fun _ => mul_nonneg zero_le_two (trDistance_nonneg _ _)

/-- Report §2.3.2 (Stage 13b decision 2) — `diamondDist Λ₁ Λ₂ ≤ 2`. -/
theorem diamondDist_le_two (Λ₁ Λ₂ : CPTPMap A B) : diamondDist Λ₁ Λ₂ ≤ 2 :=
  Real.iSup_le (fun ρ => by
    have := trDistance_le_one ((Λ₁ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ) ((Λ₂ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ)
    linarith) zero_le_two

/-- Report §2.3.2 (Stage 13b decision 2) — `diamondDist Λ Λ = 0`. -/
theorem diamondDist_self (Λ : CPTPMap A B) : diamondDist Λ Λ = 0 :=
  le_antisymm (Real.iSup_le (fun ρ => by rw [trDistance_self, mul_zero]) le_rfl)
    (diamondDist_nonneg Λ Λ)

/-- Report §2.3.2 (Stage 13b decision 2) — symmetry. -/
theorem diamondDist_comm (Λ₁ Λ₂ : CPTPMap A B) : diamondDist Λ₁ Λ₂ = diamondDist Λ₂ Λ₁ := by
  simp only [diamondDist, trDistance_symm ((Λ₁ ⊗ᶜᵖ CPTPMap.id (dIn := A)) _)]

/-- Report §2.3.2 (Stage 13b decision 2) — triangle inequality. -/
theorem diamondDist_triangle (Λ₁ Λ₂ Λ₃ : CPTPMap A B) :
    diamondDist Λ₁ Λ₃ ≤ diamondDist Λ₁ Λ₂ + diamondDist Λ₂ Λ₃ :=
  Real.iSup_le (fun ρ => by
    have h := trDistance_triangle ((Λ₁ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ) ((Λ₂ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ)
      ((Λ₃ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ)
    have h₁ := le_ciSup (diamondDist_bddAbove Λ₁ Λ₂) ρ
    have h₂ := le_ciSup (diamondDist_bddAbove Λ₂ Λ₃) ρ
    unfold diamondDist
    linarith)
    (add_nonneg (diamondDist_nonneg _ _) (diamondDist_nonneg _ _))

/-- Report §2.3.2 — the reference system is invisible after the partial trace:
`tr_R ((Λ ⊗ id) (ρ ⊗ σ)) = Λ ρ`. -/
theorem traceRight_prod_id_apply (Λ : CPTPMap A B) (ρ σ : MState A) :
    (CPTPMap.traceRight (d₁ := B) (d₂ := A)) ((Λ ⊗ᶜᵖ CPTPMap.id (dIn := A)) (ρ ⊗ᴹ σ)) = Λ ρ := by
  rw [CPTPMap.prod_apply_prod, CPTPMap.id_MState, CPTPMap.traceRight_eq_MState_traceRight,
    MState.traceRight_prod_eq]

/-- Report §2.3.2, §9.3 (Stage 13b decision 3) — **the domination lemma**
`‖Λ₁ρ − Λ₂ρ‖₁ ≤ ‖Λ₁ − Λ₂‖⋄`, i.e. `2 · TrDistance (Λ₁ ρ) (Λ₂ ρ) ≤ diamondDist Λ₁ Λ₂`.
Proof: the input `ρ ⊗ ρ` (any state on the reference works; `ρ` itself avoids a `Nonempty A`
hypothesis), the identity `tr_R ((Λ ⊗ id) (ρ ⊗ ρ)) = Λ ρ`, and data processing
(`trDistance_cptp_le`) for the partial trace `CPTPMap.traceRight`. -/
theorem diamond_dominates (Λ₁ Λ₂ : CPTPMap A B) (ρ : MState A) :
    2 * TrDistance (Λ₁ ρ) (Λ₂ ρ) ≤ diamondDist Λ₁ Λ₂ := by
  have hdp := trDistance_cptp_le (CPTPMap.traceRight (d₁ := B) (d₂ := A))
    ((Λ₁ ⊗ᶜᵖ CPTPMap.id (dIn := A)) (ρ ⊗ᴹ ρ)) ((Λ₂ ⊗ᶜᵖ CPTPMap.id (dIn := A)) (ρ ⊗ᴹ ρ))
  rw [traceRight_prod_id_apply, traceRight_prod_id_apply] at hdp
  have hsup := le_ciSup (diamondDist_bddAbove Λ₁ Λ₂) (ρ ⊗ᴹ ρ)
  unfold diamondDist
  linarith

variable {C : Type} [Fintype C] [DecidableEq C]

set_option maxRecDepth 1000 in -- as for Physlib's `CPTPMap.prod`
omit [DecidableEq C] in
/-- Report §2.3.2 — `(Ψ ∘ Φ) ⊗ id = (Ψ ⊗ id) ∘ (Φ ⊗ id)` (`MatrixMap.kron_comp_distrib`). -/
theorem prod_id_compose (Ψ : CPTPMap B C) (Φ : CPTPMap A B) :
    (Ψ ∘ₘ Φ) ⊗ᶜᵖ CPTPMap.id (dIn := A) =
      (Ψ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ∘ₘ (Φ ⊗ᶜᵖ CPTPMap.id (dIn := A)) := by
  apply CPTPMap.ext
  exact MatrixMap.kron_comp_distrib Φ.map Ψ.map LinearMap.id LinearMap.id

/-- Report §2.3.2 (Stage 13b decision 4, optional) — data processing for the diamond distance:
post-composing both channels with the same channel `Ψ` does not increase it. -/
theorem diamondDist_compose_le (Ψ : CPTPMap B C) (Φ₁ Φ₂ : CPTPMap A B) :
    diamondDist (Ψ ∘ₘ Φ₁) (Ψ ∘ₘ Φ₂) ≤ diamondDist Φ₁ Φ₂ :=
  Real.iSup_le (fun ρ => by
    rw [prod_id_compose, prod_id_compose, CPTPMap.compose_eq, CPTPMap.compose_eq]
    have hdp := trDistance_cptp_le (Ψ ⊗ᶜᵖ CPTPMap.id (dIn := A))
      ((Φ₁ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ) ((Φ₂ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ)
    have hsup := le_ciSup (diamondDist_bddAbove Φ₁ Φ₂) ρ
    unfold diamondDist
    linarith)
    (diamondDist_nonneg _ _)

end CQRV

end

end
