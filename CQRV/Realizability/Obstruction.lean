module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Card

/-!
# CQRV.Realizability.Obstruction

Report §2.2.2 — Theorem 3.1 (revised: `Cl_det`, non-degeneracy), in the report's concrete
"equivalently" form, and its two variants of revision task R1 (REVIEW_RESPONSE_1 row 8).

Neither Mathlib nor Physlib has the category U, so the categorical packaging (no monoidal
functor `Cl_det → U` preserving the copy/discard structure (Δ, !)) is deferred
(docs/DECISIONS.md, 2026-10-23). What is stated here is its linear-algebra core, in three forms:

* `no_cloning_obstruction` (Stage 2, unchanged): on a non-degenerate space (`2 ≤ |d|`) no linear
  map `C : ℂ^d → ℂ^(d×d)` copies every vector, `C ψ = ψ ⊗ ψ`. Proof: copying is not additive
  (`C (e_i + e_j)` against `C e_i + C e_j` at the index `(i, j)`).
* `no_cloning_linear` (R1 (a)): the same conclusion for **every non-empty** `d`, by scaling —
  `C (2 ψ)` is `4 ψ ⊗ ψ` while `2 C ψ` is `2 ψ ⊗ ψ`. The hypothesis `2 ≤ |d|` is therefore not
  needed for the linear-map statement; it is an artefact of the additivity proof.
* `no_cloning_pure` (R1 (b)): the **physically meaningful** form. States are density operators, and a
  physical copier is a linear map `Φ` on operators, required to copy only the **normalized pure
  states** `|ψ⟩⟨ψ|` (`∑ |ψ_k|² = 1`): `Φ |ψ⟩⟨ψ| = |ψ⟩⟨ψ| ⊗ |ψ⟩⟨ψ|`. Scaling is no longer available
  (the hypothesis is not closed under it), and the obstruction is the superposition argument: with
  `ψ± = (e_i ± e_j)/√2`, `P₊ + P₋ = E_ii + E_jj`, so by linearity `Φ P₊ + Φ P₋ = E_ii ⊗ E_ii +
  E_jj ⊗ E_jj`, whose entry at row `(i, i)`, column `(j, j)` is `0`, while the left side's is
  `(1/2)² + (−1/2)² = 1/2`. This needs two distinct basis states, and
* `pure_cloning_of_card_one` (R1 (c), sharpness) shows it cannot do without them: for `|d| = 1`
  the map `M ↦ M ⊗ 1` copies every normalized pure state (`|ψ⟩⟨ψ| = 1` there). So `2 ≤ |d|` is
  exactly the right hypothesis for (b), and (b), not (a), is the statement the paper should make
  about physical states.

The unit-norm hypothesis of (b) and (c) is `∑ k, Complex.normSq (ψ k) = 1` (DECISIONS.md, R1).
-/

@[expose] public section

namespace CQRV

open Matrix
open scoped Kronecker

/-- Report §2.2.2, Theorem 3.1 (concrete form) — for a finite basis type `d` with
`2 ≤ |d|` (non-degeneracy), there is no linear map `C : ℂ^d → ℂ^(d×d)` with `C ψ = ψ ⊗ ψ`
for **all** vectors `ψ` (naturality with respect to all states, not only basis states, which
the classical copy `|x⟩ ↦ |x⟩|x⟩` does satisfy). Proof: copying is not
additive — compare `C (e_i + e_j)` with `C e_i + C e_j` at index `(i, j)` for `i ≠ j`. -/
theorem no_cloning_obstruction {d : Type} [Fintype d] (hd : 2 ≤ Fintype.card d) :
    ¬ ∃ C : (d → ℂ) →ₗ[ℂ] (d × d → ℂ), ∀ ψ : d → ℂ, C ψ = fun ij => ψ ij.1 * ψ ij.2 := by
  classical
  rintro ⟨C, hC⟩
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card d)
  -- Copy is not additive: at index (i, j), `C (e_i + e_j)` gives 1, `C e_i + C e_j` gives 0.
  have h := congrFun (C.map_add (Pi.single i 1) (Pi.single j 1)) (i, j)
  rw [hC, Pi.add_apply, hC, hC] at h
  simp [hij, Ne.symm hij] at h

/-- R1 (a), REVIEW_RESPONSE_1 row 8 — **the linear-map form needs only a non-empty space**: for
every `[Nonempty d]` there is no linear `C` with `C ψ = ψ ⊗ ψ` for all `ψ`. Proof by scaling: at
`ψ = e_i` and the index `(i, i)`, `C (2 • ψ)` gives `4` while `2 • C ψ` gives `2`. -/
theorem no_cloning_linear {d : Type} [Fintype d] [Nonempty d] :
    ¬ ∃ C : (d → ℂ) →ₗ[ℂ] (d × d → ℂ), ∀ ψ : d → ℂ, C ψ = fun ij => ψ ij.1 * ψ ij.2 := by
  classical
  rintro ⟨C, hC⟩
  obtain ⟨i⟩ := ‹Nonempty d›
  have h := congrFun (C.map_smul (2 : ℂ) (Pi.single i 1)) (i, i)
  rw [hC, hC] at h
  simp at h

/-- `1/√2` as a complex number. -/
noncomputable def invSqrt2 : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

theorem invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  rw [invSqrt2, ← Complex.ofReal_mul, ← sq, inv_pow, Real.sq_sqrt (by norm_num)]
  push_cast; ring

theorem invSqrt2_star : star invSqrt2 = invSqrt2 := by
  rw [invSqrt2, Complex.star_def]; exact Complex.conj_ofReal _

theorem normSq_invSqrt2 : Complex.normSq invSqrt2 = 1 / 2 := by
  rw [invSqrt2, Complex.normSq_ofReal, ← sq, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- The superposition `(e_i + s e_j)/√2` as a vector; `s = ±1` gives the two states of the
no-cloning argument. -/
noncomputable def superVec {d : Type} [DecidableEq d] (i j : d) (s : ℂ) : d → ℂ :=
  fun k => if k = i then invSqrt2 else if k = j then s * invSqrt2 else 0

/-- `e_i` is a normalized state. -/
theorem single_normSq_sum {d : Type} [Fintype d] [DecidableEq d] (i : d) :
    ∑ k, Complex.normSq ((Pi.single i (1 : ℂ) : d → ℂ) k) = 1 := by
  rw [Fintype.sum_eq_single i]
  · simp
  · intro k hk; simp [hk]

/-- `(e_i + s e_j)/√2` is a normalized state for `i ≠ j` and `|s| = 1`. -/
theorem superVec_normSq_sum {d : Type} [Fintype d] [DecidableEq d] {i j : d} (hij : i ≠ j) {s : ℂ}
    (hs : Complex.normSq s = 1) : ∑ k, Complex.normSq (superVec i j s k) = 1 := by
  rw [Fintype.sum_eq_add i j hij]
  · simp [superVec, Ne.symm hij, Complex.normSq_mul, hs, normSq_invSqrt2]; norm_num
  · rintro k ⟨hki, hkj⟩; simp [superVec, hki, hkj]

/-- `P₊ + P₋ = E_ii + E_jj` for the two superpositions and the two basis states. -/
theorem superVec_pure_add {d : Type} [Fintype d] [DecidableEq d] {i j : d} (hij : i ≠ j) :
    vecMulVec (superVec i j 1) (star (superVec i j 1)) +
        vecMulVec (superVec i j (-1)) (star (superVec i j (-1))) =
      vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ))) +
        vecMulVec (Pi.single j (1 : ℂ)) (star (Pi.single j (1 : ℂ))) := by
  ext k l
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  by_cases hk : k = i <;> by_cases hk' : k = j <;> by_cases hl : l = i <;> by_cases hl' : l = j
  all_goals first
    | exact absurd (hk.symm.trans hk') hij
    | exact absurd (hl.symm.trans hl') hij
    | norm_num [superVec, Pi.single_apply, hk, hk', hl, hl', hij, Ne.symm hij, invSqrt2_star,
        invSqrt2_mul_self]

/-- R1 (b), REVIEW_RESPONSE_1 row 8 — **no-cloning of normalized pure states** (the physically
meaningful form): for `2 ≤ |d|` there is no ℂ-linear map `Φ` on operators with
`Φ |ψ⟩⟨ψ| = |ψ⟩⟨ψ| ⊗ |ψ⟩⟨ψ|` for every unit vector `ψ` (`∑ |ψ_k|² = 1`). Proof: with
`ψ± = (e_i ± e_j)/√2`, `P₊ + P₋ = E_ii + E_jj` (`superVec_pure_add`), so by linearity
`Φ P₊ + Φ P₋ = E_ii ⊗ E_ii + E_jj ⊗ E_jj`; at row `(i, i)`, column `(j, j)` the right side is `0`
and the left side is `(P₊)_{ij}² + (P₋)_{ij}² = 1/4 + 1/4`. -/
theorem no_cloning_pure {d : Type} [Fintype d] [DecidableEq d] (hd : 2 ≤ Fintype.card d) :
    ¬ ∃ Φ : Matrix d d ℂ →ₗ[ℂ] Matrix (d × d) (d × d) ℂ,
      ∀ ψ : d → ℂ, ∑ k, Complex.normSq (ψ k) = 1 →
        Φ (vecMulVec ψ (star ψ)) = vecMulVec ψ (star ψ) ⊗ₖ vecMulVec ψ (star ψ) := by
  rintro ⟨Φ, hΦ⟩
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card d)
  have hsum : Φ (vecMulVec (superVec i j 1) (star (superVec i j 1))) +
      Φ (vecMulVec (superVec i j (-1)) (star (superVec i j (-1)))) =
      vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ))) ⊗ₖ
          vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ))) +
        vecMulVec (Pi.single j (1 : ℂ)) (star (Pi.single j (1 : ℂ))) ⊗ₖ
          vecMulVec (Pi.single j (1 : ℂ)) (star (Pi.single j (1 : ℂ))) := by
    rw [← map_add, superVec_pure_add hij, map_add, hΦ _ (single_normSq_sum i),
      hΦ _ (single_normSq_sum j)]
  rw [hΦ _ (superVec_normSq_sum hij (by simp)), hΦ _ (superVec_normSq_sum hij (by simp))] at hsum
  have key := congrFun (congrFun hsum (i, i)) (j, j)
  simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    at key
  norm_num [superVec, Pi.single_apply, hij, Ne.symm hij, invSqrt2_star, invSqrt2_mul_self] at key

/-- R1 (c), sharpness — on a one-point space the pure-state copier **exists**: `Φ M = M ⊗ 1` copies
every normalized pure state, because `|ψ⟩⟨ψ| = 1` there. So the hypothesis `2 ≤ |d|` of
`no_cloning_pure` cannot be dropped. -/
theorem pure_cloning_of_card_one {d : Type} [Fintype d] [DecidableEq d] (hd : Fintype.card d = 1) :
    ∃ Φ : Matrix d d ℂ →ₗ[ℂ] Matrix (d × d) (d × d) ℂ,
      ∀ ψ : d → ℂ, ∑ k, Complex.normSq (ψ k) = 1 →
        Φ (vecMulVec ψ (star ψ)) = vecMulVec ψ (star ψ) ⊗ₖ vecMulVec ψ (star ψ) := by
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hd
  refine ⟨{ toFun := fun M => M ⊗ₖ (1 : Matrix d d ℂ)
            map_add' := fun A B => Matrix.add_kronecker A B 1
            map_smul' := fun c A => Matrix.smul_kronecker c A 1 }, ?_⟩
  intro ψ hψ
  have hψx : Complex.normSq (ψ x) = 1 := by
    rwa [Fintype.sum_eq_single x (fun y hy => (hy (hx y)).elim)] at hψ
  have h1 : vecMulVec ψ (star ψ) = 1 := by
    ext k l
    rw [hx k, hx l]
    simp [Matrix.vecMulVec_apply, Complex.mul_conj, hψx]
  show vecMulVec ψ (star ψ) ⊗ₖ (1 : Matrix d d ℂ) = _
  rw [h1]

end CQRV

end
