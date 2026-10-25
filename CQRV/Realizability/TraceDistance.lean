module

public import CQRV.Realizability.Realizes
public import QuantumInfo.States.Mixed.TraceDistance

/-!
# CQRV.Realizability.TraceDistance

Report §2.3.2 (Theorem 3.3b, "via the variational characterization of the trace distance") —
the three trace-distance facts that Theorem 3.3b needs, for Physlib's `TrDistance = ½‖ρ − σ‖₁`:

1. `trDistance_triangle` — triangle inequality (from `Matrix.traceNorm_add_le`);
2. `trDistance_cptp_le` — data processing for every `CPTPMap`, via the Jordan decomposition
   `ρ − σ = (ρ − σ)⁺ − (ρ − σ)⁻` (Physlib `HermitianMat.posPart`/`negPart`);
3. `prob_sub_le_trDistance` — a POVM event probability moves by at most the trace distance.

Physlib (pinned commit) has none of 1–3 for `TrDistance`; they are proved here.
-/

@[expose] public section

noncomputable section

namespace CQRV

open scoped HermitianMat RealInnerProductSpace

variable {d d₂ : Type} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]

/-! ## Trace norm of a Hermitian matrix through its Jordan decomposition -/

/-- Report §2.3.2 — `‖A‖₁ = tr A⁺ + tr A⁻` for a Hermitian `A` (both sides are `∑ |λᵢ|`). -/
theorem traceNorm_eq_trace_posPart_add_negPart (A : HermitianMat d ℂ) :
    A.mat.traceNorm = A⁺.trace + A⁻.trace := by
  rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues A.H, A.posPart_eq_cfc_max,
    A.negPart_eq_cfc_min, HermitianMat.trace_cfc_eq, HermitianMat.trace_cfc_eq,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (max_zero_add_max_neg_zero_eq_abs_self _).symm

omit [DecidableEq d] in
/-- Report §2.3.2 — for `0 ≤ P`, `‖P‖₁ = tr P` (real-valued form of
`Matrix.PosSemidef.traceNorm_eq_trace`). -/
theorem traceNorm_eq_trace_of_nonneg {P : HermitianMat d ℂ} (hP : 0 ≤ P) :
    P.mat.traceNorm = P.trace := by
  have h := (HermitianMat.zero_le_iff.mp hP).traceNorm_eq_trace
  rw [← HermitianMat.trace_eq_trace_rc] at h
  exact_mod_cast h

omit [DecidableEq d] in
/-- Report §2.3.2 — `‖P − N‖₁ ≤ tr P + tr N` for `0 ≤ P`, `0 ≤ N`. -/
theorem traceNorm_sub_le_of_nonneg {P N : HermitianMat d ℂ} (hP : 0 ≤ P) (hN : 0 ≤ N) :
    (P - N).mat.traceNorm ≤ P.trace + N.trace := by
  have h := Matrix.traceNorm_add_le P.mat (-N.mat)
  rw [Matrix.traceNorm_neg, traceNorm_eq_trace_of_nonneg hP, traceNorm_eq_trace_of_nonneg hN,
    ← sub_eq_add_neg] at h
  exact h

omit [DecidableEq d₂] in
/-- Report §2.1.2 — a CPTP map preserves the trace of every Hermitian matrix. -/
theorem trace_cptp_apply (Λ : CPTPMap d d₂) (x : HermitianMat d ℂ) :
    (Λ.toPMap x).trace = x.trace := by
  have h := Λ.TP x.mat
  rw [← HermitianMat.trace_eq_trace_rc x] at h
  exact_mod_cast (HermitianMat.trace_eq_trace_rc (Λ.toPMap x)).trans h

/-- Report §2.3.2 — for states, `tr (ρ − σ)⁺ = tr (ρ − σ)⁻`, so the trace distance is
`tr (ρ − σ)⁺`. -/
theorem trDistance_eq_trace_posPart (ρ σ : MState d) :
    TrDistance ρ σ = (ρ.M - σ.M)⁺.trace := by
  have hA := traceNorm_eq_trace_posPart_add_negPart (ρ.M - σ.M)
  have h0 : (ρ.M - σ.M)⁺.trace - (ρ.M - σ.M)⁻.trace = 0 := by
    rw [← HermitianMat.trace_sub, HermitianMat.posPart_add_negPart, HermitianMat.trace_sub,
      ρ.tr, σ.tr, sub_self]
  have hm : (ρ.M - σ.M).mat = ρ.m - σ.m := by simp
  rw [hm] at hA
  simp only [TrDistance]
  linarith

/-- Report §2.3.2 — `TrDistance ρ σ ≤ 1` at any `DecidableEq` instance (Physlib's
`TrDistance.le_one` has the same instance restriction as `TrDistance.symm`). -/
theorem trDistance_le_one (ρ σ : MState d) : TrDistance ρ σ ≤ 1 := by
  have h := traceNorm_sub_le_of_nonneg ρ.nonneg σ.nonneg
  rw [ρ.tr, σ.tr] at h
  have hm : (ρ.M - σ.M).mat = ρ.m - σ.m := by simp
  rw [hm] at h
  simp only [TrDistance]
  linarith

/-! ## The three facts -/

/-- Report §2.3.2 — the trace distance is symmetric. (Physlib's `TrDistance.symm` is stated for
the classical `DecidableEq` instance, so it does not apply at a given instance.) -/
theorem trDistance_symm (ρ σ : MState d) : TrDistance ρ σ = TrDistance σ ρ := by
  simp only [TrDistance]
  rw [← Matrix.traceNorm_neg, neg_sub]


/-- Report §2.3.2, fact 1 — triangle inequality for the trace distance. -/
theorem trDistance_triangle (ρ σ τ : MState d) :
    TrDistance ρ τ ≤ TrDistance ρ σ + TrDistance σ τ := by
  have h := Matrix.traceNorm_add_le (ρ.m - σ.m) (σ.m - τ.m)
  rw [sub_add_sub_cancel] at h
  simp only [TrDistance]
  linarith

/-- Report §2.3.2, fact 2 — data processing: no CPTP map increases the trace distance.
With `A = ρ − σ = A⁺ − A⁻`: `Λρ − Λσ = ΛA⁺ − ΛA⁻` (linearity), `ΛA^± ≥ 0` (positivity) with
`tr ΛA^± = tr A^±` (trace preservation), so `‖Λρ − Λσ‖₁ ≤ tr A⁺ + tr A⁻ = ‖A‖₁`. -/
theorem trDistance_cptp_le (Λ : CPTPMap d d₂) (ρ σ : MState d) :
    TrDistance (Λ ρ) (Λ σ) ≤ TrDistance ρ σ := by
  set A := ρ.M - σ.M
  have hΛ : (Λ ρ).m - (Λ σ).m = (Λ.toPMap A⁺ - Λ.toPMap A⁻).mat := by
    rw [← map_sub, HermitianMat.posPart_add_negPart, map_sub]
    simp; rfl
  have h := traceNorm_sub_le_of_nonneg (PMap.pos_Hermitian Λ.toPMap A.posPart_nonneg)
    (PMap.pos_Hermitian Λ.toPMap A.negPart_nonneg)
  rw [← hΛ, trace_cptp_apply, trace_cptp_apply,
    ← traceNorm_eq_trace_posPart_add_negPart] at h
  have hm : A.mat = ρ.m - σ.m := by simp [A]
  rw [hm] at h
  simp only [TrDistance]
  linarith

/-- Report §2.3.2 — one-sided measurement bound: with `A = ρ − σ`, each outcome contributes
`⟪M_x, A⁺⟫ − ⟪M_x, A⁻⟫ ≤ ⟪M_x, A⁺⟫` (and `0 ≤ ⟪M_x, A⁺⟫` off the event), and
`∑ₓ ⟪M_x, A⁺⟫ = ⟪1, A⁺⟫ = tr A⁺ = TrDistance ρ σ`. -/
theorem prob_sub_le_trDistance_of {X : Type} [Fintype X] (dec : POVM X d) (ρ σ : MState d)
    (E : X → Prop) : prob (dec.measure ρ) E - prob (dec.measure σ) E ≤ TrDistance ρ σ := by
  classical
  set A := ρ.M - σ.M
  have hterm : ∀ x, ((if E x then (dec.measure ρ x : ℝ) else 0) -
      if E x then (dec.measure σ x : ℝ) else 0) ≤ ⟪dec.mats x, A⁺⟫ := by
    intro x
    have hP := HermitianMat.inner_ge_zero (dec.nonneg x) A.posPart_nonneg
    have hN := HermitianMat.inner_ge_zero (dec.nonneg x) A.negPart_nonneg
    have hd : (dec.measure ρ x : ℝ) - dec.measure σ x = ⟪dec.mats x, A⁺⟫ - ⟪dec.mats x, A⁻⟫ := by
      change ⟪dec.mats x, ρ.M⟫ - ⟪dec.mats x, σ.M⟫ = _
      rw [← HermitianMat.inner_sub_left, ← HermitianMat.inner_sub_left,
        HermitianMat.posPart_add_negPart]
    split_ifs <;> linarith
  have hsum : ∑ x, ⟪dec.mats x, A⁺⟫ = A⁺.trace := by
    rw [← sum_inner, dec.normalized, HermitianMat.one_inner]
  rw [trDistance_eq_trace_posPart, ← hsum, prob, prob, ← Finset.sum_sub_distrib]
  convert Finset.sum_le_sum fun x _ => hterm x

/-- Report §2.3.2, fact 3 — measurement bound ("variational characterization" direction): for
every POVM and event `E`, `|Pr_{dec.measure ρ}[E] − Pr_{dec.measure σ}[E]| ≤ TrDistance ρ σ`. -/
theorem prob_sub_le_trDistance {X : Type} [Fintype X] (dec : POVM X d) (ρ σ : MState d)
    (E : X → Prop) : |prob (dec.measure ρ) E - prob (dec.measure σ) E| ≤ TrDistance ρ σ := by
  rw [abs_sub_le_iff]
  exact ⟨prob_sub_le_trDistance_of dec ρ σ E,
    trDistance_symm σ ρ ▸ prob_sub_le_trDistance_of dec σ ρ E⟩

end CQRV

end

end
