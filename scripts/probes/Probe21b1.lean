import CQRV

/-!
# Probe 21b1 — measured composition (PHASE2_SPEC §A.7, §A.9 (1); STAGE21_TASK.md 21b1)

A standalone file, outside the build and CI: `lake env lean scripts/probes/Probe21b1.lean`. It holds
the statements and proof attempts of Q1 (Theorem 3.3a on a pseudo-metric), Q2 (stage 2 as a
`GradedChannel`) and Q4 (the exclusion inequality of the candidate instance), with the `#check`s
of CLAUDE.md rule 2. Nothing here is imported by `CQRV/`.
-/

namespace Probe21b1

open CQRV

/-! ## Q1 — `measured_composition` on pseudo-metric spaces -/

section Q1

variable {X Y Z dY dZ : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z] [Fintype dY] [DecidableEq dY] [Fintype dZ] [DecidableEq dZ]

/-- Theorem 3.3a with `[PseudoMetricSpace Y] [PseudoMetricSpace Z]` in place of `[MetricSpace _]`:
the proof of `measured_composition` verbatim. Every lemma it uses (`relax_comp`,
`mixture_union_bound`, `prob_mixture`, `measure_chan_ofClassical`, `prob_mono`, `Spec.relax`) is
stated on a pseudo-metric or needs no metric. -/
theorem measured_composition_pseudo [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {S_f : Spec X Y} {S_g : Spec Y Z} {dec_f : POVM Y dY} {dec_g : POVM Z dZ}
    {Φ : GradedChannel X dY} {Ψ : GradedChannel Y dZ} {ε_f ε_g δ_f δ_g : ℝ} {r s : Grade}
    (hf : Realizes S_f dec_f Φ ε_f δ_f r) (hg : Realizes S_g dec_g Ψ ε_g δ_g s)
    (hdom : ∀ x ∈ S_f.dom, ∀ y, S_f.relax ε_f x y → y ∈ S_g.dom)
    (hnonexp : ∀ y ∈ S_g.dom, ∀ y' z', S_g y' z' → ∃ z, S_g y z ∧ dist z z' ≤ dist y y')
    (hδf : 0 ≤ δ_f) (hδg : 0 ≤ δ_g) (hδg1 : δ_g ≤ 1) :
    Realizes (S_g.comp S_f) dec_g (measuredComp Φ dec_f Ψ) (ε_f + ε_g) (δ_f + δ_g) (r + s) := by
  classical
  refine ⟨Grade.seqComp_mono hf.1 hg.1, ?_⟩
  rintro x ⟨z, y, hxy, -⟩
  have hx : x ∈ S_f.dom := ⟨y, hxy⟩
  have hchan : (measuredComp Φ dec_f Ψ).chan (encode x) =
      Ψ.chan (MState.ofClassical (dec_f.measure (Φ.chan (encode x)))) := by
    simp [measuredComp, POVM.measureDiscard_apply]
  rw [hchan, prob_mixture (measure_chan_ofClassical dec_g Ψ.chan _)]
  exact mixture_union_bound (hf.2 x hx)
    (fun y' h => (hg.2 y' (hdom x hx y' h)).trans
      (prob_mono _ fun _ hz => relax_comp hdom hnonexp hx h hz))
    hδf hδg hδg1

#print axioms measured_composition_pseudo

end Q1

/-! ## Rule 2 — the names Q2 and Q4 would use -/

#check @POVM.measureDiscard
#check @POVM.measureDiscard_apply
#check @CPTPMap.replacement
#check @MState.ofClassical
#check @CPTPMap.compose
#check @CQRV.Grover.groverChannel
#check @CQRV.Grover.countPOVM
#check @CQRV.Grover.CountSpec
#check @CQRV.Grover.countSpec_relax
#check @CQRV.Grover.ae_eps
#check @CQRV.Grover.ae_delta
#check @CQRV.Grover.countEst
#check @CQRV.Synthesis.rStar
#check @CQRV.Certify.groverDelta
#check @Real.sin_bound
#check @Real.cos_bound
#check @Real.sin_lt
#check @Real.sin_le
#check @Real.sin_gt_sub_cube
#check @Real.sqrt_lt'
#check @Real.lt_sqrt
#check @Real.sqrt_lt_sqrt
#check @Real.sin_sq_le_one
#check @Real.sin_pos_of_pos_of_lt_pi
#check @Real.sin_lt_sin_of_lt_of_le_pi_div_two
#check @Real.pi_lt_d4
#check @Real.pi_gt_d4
#check @CPTPMap.CPTP_of_choi_PSD_Tr
#check @MatrixMap.of_choi_matrix
#check @CPTPMap.mat_coe_eq_apply_mat
#check @Matrix.PosSemidef.PosSemidef_kronecker
#check @Matrix.PosSemidef.add
#check @Matrix.PosSemidef.zero
#check @Matrix.posSemidef_sum
#check @MState.psd
#check @MState.tr'
#check @Matrix.traceLeft
#check @Matrix.kroneckerMap_apply
#check @MState.ext
#check @HermitianMat.ext
#check @ProbDistribution.constant_eq
#check @MState.coe_ofClassical
#check @HermitianMat.diagonal_mat

/-! ## Q2 — stage 2 as a `GradedChannel`: the measure-and-prepare channel from its Choi matrix

Physlib has no measure-and-prepare constructor (`POVM.measureDiscard` measures and re-encodes,
`CPTPMap.replacement` prepares one fixed state); it has `CPTPMap.CPTP_of_choi_PSD_Tr`, which builds
a channel from a PSD Choi matrix with the right partial trace. The channel `y ↦ σ y` has the
block-diagonal Choi matrix `∑ y, σ_y ⊗ |y⟩⟨y|`. -/

section Q2

open scoped Kronecker ComplexOrder

variable {Y dZ : Type} [Fintype Y] [DecidableEq Y] [Fintype dZ] [DecidableEq dZ]

/-- `(encode y).m` is the matrix unit at `(y, y)`. -/
theorem encode_m (y a a' : Y) : (encode y).m a a' = if a = y ∧ a' = y then 1 else 0 := by
  simp only [encode, MState.m, MState.coe_ofClassical, HermitianMat.diagonal_mat,
    Matrix.diagonal_apply, ProbDistribution.constant_eq]
  by_cases h : a = a' <;> by_cases hy : a = y <;> simp [h, hy] <;> aesop

/-- The Choi matrix of the measure-and-prepare channel `y ↦ σ y`: `∑ y, σ_y ⊗ |y⟩⟨y|`. -/
noncomputable def mpChoi (σ : Y → MState dZ) : Matrix (dZ × Y) (dZ × Y) ℂ :=
  ∑ y, (σ y).m ⊗ₖ (encode y).m

theorem mpChoi_psd (σ : Y → MState dZ) : (mpChoi σ).PosSemidef := by
  unfold mpChoi
  refine Finset.sum_induction _ _ (fun A B hA hB => hA.add hB) Matrix.PosSemidef.zero ?_
  intro y _
  exact (σ y).psd.PosSemidef_kronecker (encode y).psd

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

/-- The measure-and-prepare channel: measure the input in the computational basis of `Y`, prepare
`σ y` on `dZ`. -/
noncomputable def measurePrepare (σ : Y → MState dZ) : CPTPMap Y dZ :=
  CPTPMap.CPTP_of_choi_PSD_Tr (mpChoi_psd σ) (mpChoi_traceLeft σ)

/-- On the encoded input `y₀` the channel prepares `σ y₀`. -/
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

/-- Stage 2 of route (a) as a `GradedChannel` on `CountOut m a`: on the outcome `y` it prepares the
output of the Grover channel at `r y` iterations; its declared grade is `gmax`, to be chosen as the
maximum of the circuits' grades over the outcomes (`groverChannel` keeps the measured grade). -/
noncomputable def stage2 {n m : ℕ} {a : ℝ} (C : CQRV.Grover.CountOut m a → Circuit) (gmax : Grade) :
    GradedChannel (CQRV.Grover.CountOut m a) (Reg n) :=
  ⟨measurePrepare fun y => (CQRV.Grover.groverChannel n (C y)).chan (encode ()), gmax⟩

/-- The Q2 identity: on the encoded outcome `y`, stage 2 is the Grover channel at `C y` on `encode ()`. -/
theorem stage2_encode {n m : ℕ} {a : ℝ} (C : CQRV.Grover.CountOut m a → Circuit) (gmax : Grade)
    (y : CQRV.Grover.CountOut m a) :
    (stage2 (n := n) C gmax).chan (encode y) =
      (CQRV.Grover.groverChannel n (C y)).chan (encode ()) :=
  measurePrepare_encode _ y

#print axioms measurePrepare_encode
#print axioms stage2_encode

end Q2

/-! ## Q4 — the tightest exclusion inequality of the candidate instance

`grover_pred_037`, a = 32/256 = 1/8, m = 5: `probe_21b1.py` gives D = {3, 4, 28, 29} (all with
r(y) = 2) and the tightest excluded outcome y = 2 (↔ 30), whose estimate `sin²(2π/32)` lies
0.012365 below `a − ε_f`. The inequality is `ae_eps (1/8) 5 < |sin²(π·2/2^5) − 1/8|`; 15 such
inequalities (one per excluded y modulo y ↔ 32 − y) would be needed for the δ_g bound of route (a).
The proof uses `Real.pi_lt_d4` (π < 3.1416), `Real.sin_le` (sin x ≤ x) and a decimal bound on √(7/64). -/

section Q4

open Real

set_option profiler true in
theorem exclusion_m5_y2 :
    CQRV.Grover.ae_eps (1 / 8) 5 < |Real.sin (π * 2 / 2 ^ 5) ^ 2 - 1 / 8| := by
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hx0 : 0 ≤ π * 2 / 2 ^ 5 := by positivity
  have hs0 : 0 ≤ Real.sin (π * 2 / 2 ^ 5) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by nlinarith)
  have hs : Real.sin (π * 2 / 2 ^ 5) ≤ π * 2 / 2 ^ 5 := Real.sin_le hx0
  have hsq : Real.sin (π * 2 / 2 ^ 5) ^ 2 ≤ (π * 2 / 2 ^ 5) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have hsqrt : Real.sqrt (1 / 8 * (1 - 1 / 8)) < 0.330725 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt (1 / 8 * (1 - 1 / 8)) := Real.sqrt_nonneg _
  have hlt : Real.sin (π * 2 / 2 ^ 5) ^ 2 < 1 / 8 := by nlinarith
  rw [abs_of_neg (by linarith)]
  unfold CQRV.Grover.ae_eps
  nlinarith [mul_pos hpi0 hpi0, mul_nonneg hpi0.le hsqrt0]

#print axioms exclusion_m5_y2

end Q4

end Probe21b1
