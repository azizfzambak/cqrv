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


/-! ## Unitary channels (PHASE2_SPEC.md §A.2 (5); Stage 18c, STAGE18_TASK.md C3)

The matrix norm `‖·‖` below is the L2 operator norm `Matrix.Norms.L2Operator`, the instance
Physlib's `Matrix.traceNorm_mul_le_opNorm_traceNorm` uses, so that these lemmas compose with
Physlib's trace-norm inequalities. -/

section Unitary

open Matrix Kronecker
open scoped Matrix.Norms.L2Operator MatrixMap

variable {d : Type} [Fintype d] [DecidableEq d]

/-- `‖1‖ ≤ 1` in the L2 operator norm (the identity is the diagonal of the constant-one vector;
no `Nonempty` hypothesis). -/
theorem l2_opNorm_one_le : ‖(1 : Matrix d d ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp

/-- A unitary matrix has operator norm at most `1` (`‖U‖² = ‖Uᴴ U‖ = ‖1‖ ≤ 1`). -/
theorem l2_opNorm_le_one_of_mem_unitaryGroup {U : Matrix d d ℂ}
    (hU : U ∈ Matrix.unitaryGroup d ℂ) : ‖U‖ ≤ 1 := by
  have h : ‖U‖ * ‖U‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.mp hU]
    exact l2_opNorm_one_le
  nlinarith [norm_nonneg U]

theorem conj_one_eq_id : MatrixMap.conj (1 : Matrix d d ℂ) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp [MatrixMap.conj_apply]

set_option maxRecDepth 1000 in -- as for Physlib's `CPTPMap.prod`
/-- PHASE2_SPEC.md §A.2 (5) — the unitary channel with the identity on the reference system is
conjugation by `U ⊗ 1` (`CPTPMap.prod` is `MatrixMap.kron` of the two linear maps;
`MatrixMap.conj_kron`). -/
theorem prod_id_ofUnitary (U : 𝐔[d]) (ρ : MState (d × d)) :
    (CPTPMap.ofUnitary U ⊗ᶜᵖ CPTPMap.id (dIn := d)) ρ = ρ.uConj (Matrix.unitary_kron U 1) := by
  apply MState.ext_m
  rw [CPTPMap.mat_coe_eq_apply_mat]
  change (MatrixMap.conj (U : Matrix d d ℂ) ⊗ₖₘ LinearMap.id) ρ.m = _
  rw [← conj_one_eq_id, MatrixMap.conj_kron, MatrixMap.conj_apply]
  rfl

theorem mulVec_kronecker_one (A : Matrix d d ℂ) (x : d × d → ℂ) (i j : d) :
    ((A ⊗ₖ (1 : Matrix d d ℂ)) *ᵥ x) (i, j) = (A *ᵥ fun k => x (k, j)) i := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

/-- `∑_i ‖(A y)_i‖² ≤ ‖A‖² ∑_k ‖y_k‖²`: the operator norm on one column. -/
theorem sum_norm_sq_mulVec_le (A : Matrix d d ℂ) (y : d → ℂ) :
    ∑ i, ‖(A *ᵥ y) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ k, ‖y k‖ ^ 2 := by
  have h := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 y)
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.toEuclideanCLM_toLp] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2

/-- PHASE2_SPEC.md §A.2 (5) — `‖A ⊗ 1‖ ≤ ‖A‖`: `‖(A ⊗ 1) x‖² = ∑_j ‖A x_{·,j}‖² ≤ ‖A‖² ∑_j
‖x_{·,j}‖²` (`Fintype.sum_prod_type_right`). -/
theorem l2_opNorm_kronecker_one_le (A : Matrix d d ℂ) :
    ‖A ⊗ₖ (1 : Matrix d d ℂ)‖ ≤ ‖A‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq x, Fintype.sum_prod_type_right,
    Fintype.sum_prod_type_right, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [Matrix.ofLp_toEuclideanCLM, mulVec_kronecker_one]
  exact sum_norm_sq_mulVec_le A _

omit [Fintype d] in
theorem sub_kronecker_one (A B : Matrix d d ℂ) :
    (A - B) ⊗ₖ (1 : Matrix d d ℂ) = A ⊗ₖ 1 - B ⊗ₖ 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [sub_mul]

/-- PHASE2_SPEC.md §A.2 (5), report §2.3.2 — **the diamond distance of two unitary channels is
at most twice the operator norm of the difference**: with `W_i = U_i ⊗ 1`,
`W₁ ρ W₁ᴴ − W₂ ρ W₂ᴴ = (W₁ − W₂) ρ W₁ᴴ + W₂ ρ (W₁ − W₂)ᴴ`, `traceNorm_add_le`,
`traceNorm_mul_le_opNorm_traceNorm` / `traceNorm_mul_le_traceNorm_opNorm`, `‖ρ‖₁ = 1`,
`‖W_i‖ ≤ 1` and `‖(U − V) ⊗ 1‖ ≤ ‖U − V‖`. -/
theorem diamondDist_ofUnitary_le (U V : 𝐔[d]) :
    diamondDist (CPTPMap.ofUnitary U) (CPTPMap.ofUnitary V) ≤ 2 * ‖(U : Matrix d d ℂ) - V‖ := by
  refine Real.iSup_le (fun ρ => ?_) (by positivity)
  rw [prod_id_ofUnitary, prod_id_ofUnitary]
  set W₁ : Matrix (d × d) (d × d) ℂ := (U : Matrix d d ℂ) ⊗ₖ 1 with hW₁
  set W₂ : Matrix (d × d) (d × d) ℂ := (V : Matrix d d ℂ) ⊗ₖ 1 with hW₂
  have hm₁ : (ρ.uConj (Matrix.unitary_kron U 1)).m = W₁ * ρ.m * W₁ᴴ := rfl
  have hm₂ : (ρ.uConj (Matrix.unitary_kron V 1)).m = W₂ * ρ.m * W₂ᴴ := rfl
  have hn₁ : ‖W₁‖ ≤ 1 := l2_opNorm_le_one_of_mem_unitaryGroup (Matrix.unitary_kron U 1).prop
  have hn₂ : ‖W₂‖ ≤ 1 := l2_opNorm_le_one_of_mem_unitaryGroup (Matrix.unitary_kron V 1).prop
  have hD : ‖W₁ - W₂‖ ≤ ‖(U : Matrix d d ℂ) - V‖ := by
    rw [hW₁, hW₂, ← sub_kronecker_one]
    exact l2_opNorm_kronecker_one_le _
  have hsplit : W₁ * ρ.m * W₁ᴴ - W₂ * ρ.m * W₂ᴴ =
      (W₁ - W₂) * ρ.m * W₁ᴴ + W₂ * ρ.m * (W₁ - W₂)ᴴ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.conjTranspose_sub]
    abel
  unfold TrDistance
  rw [hm₁, hm₂, hsplit]
  have h1 := Matrix.traceNorm_add_le ((W₁ - W₂) * ρ.m * W₁ᴴ) (W₂ * ρ.m * (W₁ - W₂)ᴴ)
  have h2 := Matrix.traceNorm_mul_le_traceNorm_opNorm ((W₁ - W₂) * ρ.m) W₁ᴴ
  have h3 := Matrix.traceNorm_mul_le_opNorm_traceNorm (W₁ - W₂) ρ.m
  have h4 := Matrix.traceNorm_mul_le_traceNorm_opNorm (W₂ * ρ.m) (W₁ - W₂)ᴴ
  have h5 := Matrix.traceNorm_mul_le_opNorm_traceNorm W₂ ρ.m
  rw [Matrix.l2_opNorm_conjTranspose] at h2 h4
  rw [MState.traceNorm_eq_one, mul_one] at h3 h5
  have e2 : ((W₁ - W₂) * ρ.m * W₁ᴴ).traceNorm ≤ ‖W₁ - W₂‖ :=
    calc _ ≤ ((W₁ - W₂) * ρ.m).traceNorm * ‖W₁‖ := h2
      _ ≤ ((W₁ - W₂) * ρ.m).traceNorm * 1 :=
          mul_le_mul_of_nonneg_left hn₁ (Matrix.traceNorm_nonneg _)
      _ ≤ ‖W₁ - W₂‖ := by rw [mul_one]; exact h3
  have e4 : (W₂ * ρ.m * (W₁ - W₂)ᴴ).traceNorm ≤ ‖W₁ - W₂‖ :=
    calc _ ≤ (W₂ * ρ.m).traceNorm * ‖W₁ - W₂‖ := h4
      _ ≤ 1 * ‖W₁ - W₂‖ := mul_le_mul_of_nonneg_right (h5.trans hn₂) (norm_nonneg _)
      _ = ‖W₁ - W₂‖ := one_mul _
  linarith

end Unitary

end CQRV

end

end
