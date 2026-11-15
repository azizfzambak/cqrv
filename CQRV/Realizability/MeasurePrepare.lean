module

public import CQRV.Realizability.Realizes
public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.Channels.CPTP

/-!
# CQRV.Realizability.MeasurePrepare

Stage 21b2 (PHASE2_SPEC §A.7, §A.9 "21b1 done" Q2; report §2.3.2) — **the measure-and-prepare
channel** `ρ ↦ ∑_y ⟨y|ρ|y⟩ σ_y`: measure the input in the computational basis of `Y`, prepare the
state `σ y` on `dZ`. On the encoded basis states, `encode y ↦ σ y` (`measurePrepare_encode`), which
is the case the measured composition of Theorem 3.3a needs: after `POVM.measureDiscard` the
intermediate register holds an encoded outcome, and the second stage acts on it classically.

Physlib has no such constructor (`POVM.measureDiscard` measures and re-encodes the outcome,
`CPTPMap.replacement` prepares one fixed state, `CPTPMap.of_kraus_CPTPMap` would need the square
roots of the prepared states), but it has `CPTPMap.CPTP_of_choi_PSD_Tr`, which builds a channel
from a positive semidefinite Choi matrix with partial trace `1`. The channel `y ↦ σ y` has the
block-diagonal Choi matrix `∑ y, σ_y ⊗ |y⟩⟨y|`.
-/

@[expose] public section

noncomputable section

namespace CQRV

open scoped Kronecker ComplexOrder

variable {Y dZ : Type} [Fintype Y] [DecidableEq Y] [Fintype dZ] [DecidableEq dZ]

/-- Report §2.1.2 — `(encode y).m` is the matrix unit at `(y, y)`. -/
theorem encode_m (y a a' : Y) : (encode y).m a a' = if a = y ∧ a' = y then 1 else 0 := by
  simp only [encode, MState.m, MState.coe_ofClassical, HermitianMat.diagonal_mat,
    Matrix.diagonal_apply, ProbDistribution.constant_eq]
  by_cases h : a = a' <;> by_cases hy : a = y <;> simp [h, hy] <;> aesop

/-- Report §2.3.2 (Stage 21b2) — the Choi matrix of the measure-and-prepare channel `y ↦ σ y`:
`∑ y, σ_y ⊗ |y⟩⟨y|`, indexed as Physlib's `MatrixMap.of_choi_matrix` expects (output × input). -/
def mpChoi (σ : Y → MState dZ) : Matrix (dZ × Y) (dZ × Y) ℂ :=
  ∑ y, (σ y).m ⊗ₖ (encode y).m

/-- The Choi matrix is positive semidefinite: a sum of Kronecker products of density matrices
with projectors. -/
theorem mpChoi_psd (σ : Y → MState dZ) : (mpChoi σ).PosSemidef := by
  unfold mpChoi
  refine Finset.sum_induction _ _ (fun A B hA hB => hA.add hB) Matrix.PosSemidef.zero ?_
  intro y _
  exact (σ y).psd.PosSemidef_kronecker (encode y).psd

/-- The partial trace over the output is `∑ y, tr(σ_y) |y⟩⟨y| = 1` (trace preservation). -/
theorem mpChoi_traceLeft (σ : Y → MState dZ) : (mpChoi σ).traceLeft = 1 := by
  ext a a'
  simp only [Matrix.traceLeft, Matrix.of_apply, mpChoi, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    encode_m, Matrix.one_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  by_cases h : a = a'
  · subst h
    have htr : ∀ y, ∑ i, (σ y).m i i = 1 := fun y => by
      have := (σ y).tr'; simpa [Matrix.trace, Matrix.diag] using this
    simp [htr]
  · simp only [h, ↓reduceIte]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hx : ¬ (a = x ∧ a' = x) := fun hx => h (hx.1.trans hx.2.symm)
    simp [hx]

/-- Report §2.3.2 (Stage 21b2) — **the measure-and-prepare channel** `ρ ↦ ∑_y ⟨y|ρ|y⟩ σ_y`:
measure the input in the computational basis of `Y`, prepare `σ y` on `dZ`; built from its Choi
matrix through `CPTPMap.CPTP_of_choi_PSD_Tr`. -/
def measurePrepare (σ : Y → MState dZ) : CPTPMap Y dZ :=
  CPTPMap.CPTP_of_choi_PSD_Tr (mpChoi_psd σ) (mpChoi_traceLeft σ)

/-- Report §2.3.2 — on the encoded input `y₀` the channel prepares `σ y₀`: the case the measured
composition needs (`POVM.measureDiscard` re-encodes the outcome with `encode`). -/
theorem measurePrepare_encode (σ : Y → MState dZ) (y₀ : Y) :
    measurePrepare σ (encode y₀) = σ y₀ := by
  apply MState.ext
  apply HermitianMat.ext
  ext b₁ b₂
  change (measurePrepare σ (encode y₀)).m b₁ b₂ = (σ y₀).m b₁ b₂
  rw [CPTPMap.mat_coe_eq_apply_mat]
  show (MatrixMap.of_choi_matrix (mpChoi σ)) (encode y₀).m b₁ b₂ = _
  simp only [MatrixMap.of_choi_matrix, LinearMap.coe_mk, mpChoi, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, encode_m]
  show (∑ x, ∑ x', (encode y₀).m x x' *
      ∑ c, (σ c).m b₁ b₂ * (if x = c ∧ x' = c then (1 : ℂ) else 0)) = _
  simp only [encode_m]
  simp [ite_and, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

end CQRV

end

end
