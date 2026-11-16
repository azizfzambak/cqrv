module

public import CQRV.Grover.CountingCorrect
public import CQRV.Grover.Lemma
public import CQRV.Grover.QPEBound

/-!
# CQRV.Grover.Counting

PHASE2_SPEC.md §A.4 "Amendments before Stage 20a" (1)–(4), §A.3 (5) (`U_count`); report §2.2,
§8.2, §8.3.2; docs/tasks/STAGE20A_TASK.md B1–B4 (Stage 20a2) — **the outcome distribution of the
counting circuit and the QPE bound**, from `U_count` of Stage 19c, `iteration_induction` of Stage
7b and the analysis of Stage 20a1. Not in the `cqr` closure (it imports Physlib through
`CountingCorrect` and `Lemma`).

* B1 — `U_count_zero_apply`: the amplitude of `U_count gp.P m none` on `|0…0⟩` at `x` is
  `2^{−m} ∑_{k<2^m} e^{−2πi y k/2^m} (G^k ketS)(search x)` with `y = (phase x).toNat`. Three steps,
  right to left: the Hadamard layer on `|0…0⟩` is the constant `ketS (n+m)` (no split of
  `hadamardMat (n+m)` into `liftS · liftP` is needed); `ctrlPow` on a constant is `2^{−m/2}`
  times `G^{(phase x).toNatLE} ketS` on the search register (`ctrlPow_mulVec_const`); the inverse
  QFT row through `dataMat_apply`, `qft_basis` and `Reg.toNat_bitRev` (`star_dataMat_qft_apply`);
  then the sum over `Reg m` is reindexed by `toNatLE` (`Reg.sum_toNatLE`, Basis.lean).
* B2 — the two phases, with no eigenvectors (amendment (1)): `iteration_induction` writes
  `G^k ketS = sin((2k+1)θ) ψ_g + cos((2k+1)θ) ψ_b`, so the amplitude is `ampA y · ψ_g + ampB y ·
  ψ_b` (`U_count_zero_apply_eq`); sine and cosine as exponentials give `ampA_eq` / `ampB_eq` in terms
  of `D₊ = qpeAmp m (θ/π − y/2^m)` and `D₋ = qpeAmp m (−θ/π − y/2^m)`, and the parallelogram law
  gives `‖ampA‖² + ‖ampB‖² = (‖D₊‖² + ‖D₋‖²)/2` (`norm_sq_ampA_add_ampB`).
* B3 — `phaseDist gp m y = ∑_s ‖amplitude (s, y)‖²` and `phaseDist_eq : phaseDist = ½ (qpeProb m
  (θ/π) y.toNat + qpeProb m (−θ/π) y.toNat)` for every `GroverData`, `M = 2ⁿ` included: there
  `ψ_b = 0` (`psiBad_dot_self`), `θ = π/2`, and `ampB = 0` because `D₋ = D₊` (period 1) and
  `e^{iπ/2} + e^{−iπ/2} = 0` (`ampB_eq_zero_of_psiBad`). No hypothesis `M < 2ⁿ`.
* B4 — `qpe_two_phase_bound` (the outcomes near `θ/π` or `−θ/π` carry `≥ 8/π²`, from
  `qpe_near_sum_ge` once per sign, reindexed through `Reg.sum_toNat`) and `qpe_success` (the
  outcomes whose decoding `sin²(π y/2^m)` is within `ae_eps (M/2ⁿ) m` of `M/2ⁿ` carry `≥ 8/π²`,
  from `decode_close` and `sin_θ_eq`). Both filters use the decidability instance of
  `qpe_near_sum_ge` (`open Classical in`). Stage 20b works from `qpe_success`.
A list that follows a newline is parenthesised (PHASE2_SPEC §A.8 item 6).
-/

@[expose] public section

namespace CQRV.Grover

open CQRV CQRV.Synthesis CQRV.Counting Matrix Real

/-! ## B1 — the amplitude of `U_count` on `|0…0⟩` -/

theorem search_symm {n m : ℕ} (s : Reg n) (p : Reg m) :
    search ((splitEquiv n m).symm (s, p)) = s := by
  have h := (splitEquiv n m).apply_symm_apply (s, p)
  rw [splitEquiv_apply] at h
  exact (Prod.mk.inj h).1

theorem phase_symm {n m : ℕ} (s : Reg n) (p : Reg m) :
    phase ((splitEquiv n m).symm (s, p)) = p := by
  have h := (splitEquiv n m).apply_symm_apply (s, p)
  rw [splitEquiv_apply] at h
  exact (Prod.mk.inj h).2

/-- `ctrlPow V` on a constant vector: `V ^ (phase x).toNatLE` applied to the constant on the
search register. -/
theorem ctrlPow_mulVec_const {n m : ℕ} (V : Matrix (Reg n) (Reg n) ℂ) (c : ℂ)
    (x : Reg (n + m)) :
    (ctrlPow V *ᵥ fun _ => c) x = ∑ s : Reg n, (V ^ (phase x).toNatLE) (search x) s * c := by
  simp only [Matrix.mulVec, dotProduct, ctrlPow_apply]
  rw [← Equiv.sum_comp (splitEquiv n m).symm, Fintype.sum_prod_type]
  simp only [search_symm, phase_symm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- `liftP B` applied to a vector: the row of `B` at the phase register, the vector read on the
search register of `x`. -/
theorem liftP_mulVec {n m : ℕ} (B : Matrix (Reg m) (Reg m) ℂ) (w : Reg (n + m) → ℂ)
    (x : Reg (n + m)) :
    (liftP B *ᵥ w) x = ∑ p : Reg m, B (phase x) p * w ((splitEquiv n m).symm (search x, p)) := by
  simp only [Matrix.mulVec, dotProduct, liftP_apply]
  rw [← Equiv.sum_comp (splitEquiv n m).symm, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [search_symm, phase_symm, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]

/-- The inverse QFT row: `(QFT†)_{q p} = 2^{−m/2} e^{−2πi q.toNat · p.toNatLE / 2^m}`
(`dataMat_apply`, `qft_basis`, `Reg.toNat_bitRev`). -/
theorem star_dataMat_qft_apply (m : ℕ) (q p : Reg m) :
    star (dataMat m (qftGates m)) q p =
      ((Real.sqrt 2)⁻¹ : ℂ) ^ m *
        Complex.exp (-(2 * π * Complex.I * q.toNat * p.toNatLE / 2 ^ m)) := by
  rw [Matrix.star_apply, dataMat_apply,
    ← mulVec_basisVec (unitaryDenote m 0 (qftGates m)) (p, reg0) (q, reg0), qft_basis,
    Reg.toNat_bitRev,
    Complex.star_def, map_mul, map_pow, map_inv₀, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_div₀, map_mul, map_natCast, map_pow, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  push_cast
  ring

theorem invSqrtTwo_pow_mul_self (m : ℕ) :
    ((Real.sqrt 2)⁻¹ : ℂ) ^ m * ((Real.sqrt 2)⁻¹ : ℂ) ^ m = ((2 ^ m : ℕ) : ℂ)⁻¹ := by
  rw [← mul_pow, invSqrtTwo_mul_self, one_div, inv_pow]
  push_cast
  rfl

/-- B1 (PHASE2_SPEC.md §A.4 (2)) — the amplitude of the counting circuit's unitary on `|0…0⟩`:
`2^{−m} ∑_{k<2^m} e^{−2πi y k/2^m} (G^k ketS)(search x)`, `y = (phase x).toNat`. -/
theorem U_count_zero_apply (gp : GroverData) (m : ℕ) (x : Reg (gp.n + m)) :
    ((U_count gp.P m none).val *ᵥ basisVec (zeroReg _)) x =
      ((2 ^ m : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 ^ m),
        Complex.exp (-(2 * π * Complex.I * (phase x).toNat * k / 2 ^ m)) *
          ((groverOp gp.P ^ k).val *ᵥ ketS gp.n) (search x) := by
  -- (i) the Hadamard layer on |0…0⟩ is the constant `ketS (n + m)`
  have h1 : (U_count gp.P m none).val *ᵥ basisVec (zeroReg (gp.n + m)) =
      liftP (star (dataMat m (qftGates m))) *ᵥ
        (ctrlPow (groverOp gp.P).val *ᵥ ketS (gp.n + m)) := by
    show (liftP (star (dataMat m (inverseGates m none))) * ctrlPow (groverOp gp.P).val *
      hadamardMat (gp.n + m)) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hadamardMat_mulVec_zero]
    rfl
  -- (ii) `ctrlPow` on the constant
  have h2 : ∀ z : Reg (gp.n + m), (ctrlPow (groverOp gp.P).val *ᵥ ketS (gp.n + m)) z =
      ((Real.sqrt 2)⁻¹ : ℂ) ^ m *
        (((groverOp gp.P).val ^ (phase z).toNatLE) *ᵥ ketS gp.n) (search z) := by
    intro z
    rw [show ketS (gp.n + m) = fun _ => ((Real.sqrt 2)⁻¹ : ℂ) ^ (gp.n + m) from rfl,
      ctrlPow_mulVec_const]
    simp only [Matrix.mulVec, dotProduct, ketS, pow_add]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  -- (iii) the inverse QFT row, then the reindexing of `∑ p : Reg m` by `toNatLE`
  rw [h1, liftP_mulVec]
  have key : ∀ p : Reg m, star (dataMat m (qftGates m)) (phase x) p *
      (ctrlPow (groverOp gp.P).val *ᵥ ketS (gp.n + m)) ((splitEquiv gp.n m).symm (search x, p)) =
      ((2 ^ m : ℕ) : ℂ)⁻¹ *
        (Complex.exp (-(2 * π * Complex.I * (phase x).toNat * p.toNatLE / 2 ^ m)) *
          (((groverOp gp.P).val ^ p.toNatLE) *ᵥ ketS gp.n) (search x)) := by
    intro p
    rw [star_dataMat_qft_apply, h2, phase_symm, search_symm, ← invSqrtTwo_pow_mul_self]
    ring
  rw [Finset.sum_congr rfl (fun p _ => key p),
    Reg.sum_toNatLE m (fun k => ((2 ^ m : ℕ) : ℂ)⁻¹ *
      (Complex.exp (-(2 * π * Complex.I * (phase x).toNat * k / 2 ^ m)) *
        (((groverOp gp.P).val ^ k) *ᵥ ketS gp.n) (search x))),
    Finset.mul_sum]
  rfl

/-! ## B2 — the two phases -/

/-- The amplitude of `ψ_g`: `2^{−m} ∑_k e^{−2πi y k/2^m} sin((2k+1)θ)`. -/
noncomputable def ampA (gp : GroverData) (m y : ℕ) : ℂ :=
  ((2 ^ m : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 ^ m),
    Complex.exp (-(2 * π * Complex.I * y * k / 2 ^ m)) * (Real.sin ((2 * k + 1) * gp.θ) : ℂ)

/-- The amplitude of `ψ_b`: `2^{−m} ∑_k e^{−2πi y k/2^m} cos((2k+1)θ)`. -/
noncomputable def ampB (gp : GroverData) (m y : ℕ) : ℂ :=
  ((2 ^ m : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 ^ m),
    Complex.exp (-(2 * π * Complex.I * y * k / 2 ^ m)) * (Real.cos ((2 * k + 1) * gp.θ) : ℂ)

/-- B2 — the amplitude at `x` is `ampA y · ψ_g (search x) + ampB y · ψ_b (search x)`
(`iteration_induction`, no eigenvectors). -/
theorem U_count_zero_apply_eq (gp : GroverData) (m : ℕ) (x : Reg (gp.n + m)) :
    ((U_count gp.P m none).val *ᵥ basisVec (zeroReg _)) x =
      ampA gp m (phase x).toNat * gp.psiGood (search x) +
        ampB gp m (phase x).toNat * gp.psiBad (search x) := by
  rw [U_count_zero_apply]
  unfold ampA ampB
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [GroverData.iteration_induction]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The exponential of the shifted phase: `e^{−2πi y k/2^m} e^{±i(2k+1)θ} = e^{±iθ} e^{2πi k δ±}`. -/
theorem exp_shift (gp : GroverData) (m y k : ℕ) (σ : ℝ) :
    Complex.exp (-(2 * π * Complex.I * y * k / 2 ^ m)) *
        Complex.exp (((σ * ((2 * k + 1) * gp.θ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((σ * gp.θ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (2 * π * Complex.I * k * ((σ * gp.θ / π - y / 2 ^ m : ℝ) : ℂ)) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  have h2 : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  push_cast
  field_simp
  ring

/-- B2 — `ampA y = (e^{iθ} D₊ − e^{−iθ} D₋) / (2i)`. -/
theorem ampA_eq (gp : GroverData) (m y : ℕ) :
    ampA gp m y =
      (Complex.exp ((gp.θ : ℂ) * Complex.I) * qpeAmp m (gp.θ / π - y / 2 ^ m) -
        Complex.exp ((-gp.θ : ℂ) * Complex.I) * qpeAmp m (-gp.θ / π - y / 2 ^ m)) /
        (2 * Complex.I) := by
  unfold ampA qpeAmp
  have hterm : ∀ k ∈ Finset.range (2 ^ m),
      Complex.exp (-(2 * π * Complex.I * y * k / 2 ^ m)) * (Real.sin ((2 * k + 1) * gp.θ) : ℂ) =
        (Complex.exp ((gp.θ : ℂ) * Complex.I) *
            Complex.exp (2 * π * Complex.I * k * ((gp.θ / π - y / 2 ^ m : ℝ) : ℂ)) -
          Complex.exp ((-gp.θ : ℂ) * Complex.I) *
            Complex.exp (2 * π * Complex.I * k * ((-gp.θ / π - y / 2 ^ m : ℝ) : ℂ))) /
          (2 * Complex.I) := by
    intro k _
    have hA := exp_shift gp m y k 1
    have hB := exp_shift gp m y k (-1)
    simp only [one_mul, neg_one_mul, Complex.ofReal_neg] at hA hB
    have hI2 : (2 * Complex.I : ℂ)⁻¹ = -Complex.I / 2 := by
      rw [mul_inv, Complex.inv_I]
      ring
    rw [Complex.ofReal_sin, Complex.sin, div_eq_mul_inv _ (2 * Complex.I), hI2]
    linear_combination (-(Complex.I / 2)) * hA + (Complex.I / 2) * hB
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

/-- B2 — `ampB y = (e^{iθ} D₊ + e^{−iθ} D₋) / 2`. -/
theorem ampB_eq (gp : GroverData) (m y : ℕ) :
    ampB gp m y =
      (Complex.exp ((gp.θ : ℂ) * Complex.I) * qpeAmp m (gp.θ / π - y / 2 ^ m) +
        Complex.exp ((-gp.θ : ℂ) * Complex.I) * qpeAmp m (-gp.θ / π - y / 2 ^ m)) / 2 := by
  unfold ampB qpeAmp
  have hterm : ∀ k ∈ Finset.range (2 ^ m),
      Complex.exp (-(2 * π * Complex.I * y * k / 2 ^ m)) * (Real.cos ((2 * k + 1) * gp.θ) : ℂ) =
        (Complex.exp ((gp.θ : ℂ) * Complex.I) *
            Complex.exp (2 * π * Complex.I * k * ((gp.θ / π - y / 2 ^ m : ℝ) : ℂ)) +
          Complex.exp ((-gp.θ : ℂ) * Complex.I) *
            Complex.exp (2 * π * Complex.I * k * ((-gp.θ / π - y / 2 ^ m : ℝ) : ℂ))) / 2 := by
    intro k _
    have hA := exp_shift gp m y k 1
    have hB := exp_shift gp m y k (-1)
    simp only [one_mul, neg_one_mul, Complex.ofReal_neg] at hA hB
    rw [Complex.ofReal_cos, Complex.cos]
    linear_combination (1 / 2 : ℂ) * hA + (1 / 2 : ℂ) * hB
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

/-- B2 — `‖ampA‖² + ‖ampB‖² = (‖D₊‖² + ‖D₋‖²)/2` (the parallelogram law; `|e^{±iθ}| = 1`). -/
theorem norm_sq_ampA_add_ampB (gp : GroverData) (m y : ℕ) :
    ‖ampA gp m y‖ ^ 2 + ‖ampB gp m y‖ ^ 2 =
      (‖qpeAmp m (gp.θ / π - y / 2 ^ m)‖ ^ 2 + ‖qpeAmp m (-gp.θ / π - y / 2 ^ m)‖ ^ 2) / 2 := by
  rw [ampA_eq, ampB_eq]
  have hu : ‖Complex.exp ((gp.θ : ℂ) * Complex.I) * qpeAmp m (gp.θ / π - y / 2 ^ m)‖ =
      ‖qpeAmp m (gp.θ / π - y / 2 ^ m)‖ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hv : ‖Complex.exp ((-gp.θ : ℂ) * Complex.I) * qpeAmp m (-gp.θ / π - y / 2 ^ m)‖ =
      ‖qpeAmp m (-gp.θ / π - y / 2 ^ m)‖ := by
    rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hp := parallelogram_law_with_norm ℝ
    (Complex.exp ((gp.θ : ℂ) * Complex.I) * qpeAmp m (gp.θ / π - y / 2 ^ m))
    (Complex.exp ((-gp.θ : ℂ) * Complex.I) * qpeAmp m (-gp.θ / π - y / 2 ^ m))
  rw [hu, hv] at hp
  rw [norm_div, norm_div, norm_mul, Complex.norm_two, Complex.norm_I, mul_one, div_pow, div_pow]
  have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
  rw [h4]
  linarith

/-! ## B3 — the distribution -/

/-- PHASE2_SPEC.md §A.4 (3) — the distribution of the phase register: the probability of the
outcome `y : Reg m`, marginal over the search register, on the state `U_count |0…0⟩`. -/
noncomputable def phaseDist (gp : GroverData) (m : ℕ) (y : Reg m) : ℝ :=
  ∑ s : Reg gp.n, ‖((U_count gp.P m none).val *ᵥ basisVec (zeroReg _))
    ((splitEquiv gp.n m).symm (s, y))‖ ^ 2

theorem sum_normSq_psiGood (gp : GroverData) : ∑ s, Complex.normSq (gp.psiGood s) = 1 := by
  have h := gp.psiGood_dot_self
  simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self] at h
  have h' := congrArg Complex.re h
  simpa [Complex.re_sum] using h'

theorem sum_normSq_psiBad (gp : GroverData) (hb : star gp.psiBad ⬝ᵥ gp.psiBad = 1) :
    ∑ s, Complex.normSq (gp.psiBad s) = 1 := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self] at hb
  have h' := congrArg Complex.re hb
  simpa [Complex.re_sum] using h'

theorem sum_psiGood_mul_conj_psiBad (gp : GroverData) :
    ∑ s, gp.psiGood s * (starRingEnd ℂ) (gp.psiBad s) = 0 := by
  have h := gp.psiGood_dot_psiBad
  simp only [dotProduct, Pi.star_apply, Complex.star_def] at h
  have h' := congrArg (starRingEnd ℂ) h
  rw [map_sum, map_zero] at h'
  simpa [map_mul, Complex.conj_conj] using h'

/-- `∑_s ‖A ψ_g s + B ψ_b s‖² = ‖A‖² + ‖B‖²` when `ψ_b` is a unit vector. -/
theorem sum_norm_sq_combo (gp : GroverData) (A B : ℂ) (hb : star gp.psiBad ⬝ᵥ gp.psiBad = 1) :
    ∑ s, ‖A * gp.psiGood s + B * gp.psiBad s‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_add, map_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_normSq_psiGood, sum_normSq_psiBad gp hb, mul_one, mul_one]
  have e : ∀ s, A * gp.psiGood s * ((starRingEnd ℂ) B * (starRingEnd ℂ) (gp.psiBad s)) =
      (A * (starRingEnd ℂ) B) * (gp.psiGood s * (starRingEnd ℂ) (gp.psiBad s)) := fun s => by ring
  simp_rw [e]
  rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.mul_sum, sum_psiGood_mul_conj_psiBad, mul_zero,
    Complex.zero_re, mul_zero, add_zero]

/-- `∑_s ‖A ψ_g s‖² = ‖A‖²`. -/
theorem sum_norm_sq_good (gp : GroverData) (A : ℂ) :
    ∑ s, ‖A * gp.psiGood s‖ ^ 2 = ‖A‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_mul]
  rw [← Finset.mul_sum, sum_normSq_psiGood, mul_one]

/-- `ψ_b = 0` only at `M = 2ⁿ`, and then `θ = π/2`. -/
theorem θ_eq_pi_div_two_of_psiBad (gp : GroverData) (h : gp.psiBad = 0) : gp.θ = π / 2 := by
  have hM : gp.M = 2 ^ gp.n := by
    rcases (gp.M_le).lt_or_eq with hlt | heq
    · exfalso
      have hcard : 0 < (Finset.univ.filter (fun x => ¬ gp.P x = true)).card := by
        rw [gp.card_bad]
        omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
      rw [Finset.mem_filter] at hx
      have h0 : gp.psiBad x = 0 := by rw [h]; rfl
      simp only [GroverData.psiBad, hx.2, Bool.false_eq_true, ↓reduceIte, inv_eq_zero] at h0
      exact gp.sqrtB_ne_of_bad hx.2 h0
    · exact heq
  rw [GroverData.θ, hM]
  push_cast
  rw [div_self (by positivity), Real.sqrt_one, Real.arcsin_one]

/-- At `M = 2ⁿ` the amplitude of `ψ_b` vanishes: `θ = π/2`, `D₋ = D₊` (period 1 of `qpeAmp`),
and `e^{iπ/2} + e^{−iπ/2} = 0`. -/
theorem ampB_eq_zero_of_psiBad (gp : GroverData) (m y : ℕ) (h : gp.psiBad = 0) :
    ampB gp m y = 0 := by
  rw [ampB_eq, θ_eq_pi_div_two_of_psiBad gp h]
  have hD : qpeAmp m (-(π / 2) / π - y / 2 ^ m) = qpeAmp m (π / 2 / π - y / 2 ^ m) := by
    have e : (-(π / 2) / π - y / 2 ^ m : ℝ) = (π / 2 / π - y / 2 ^ m) + ((-1 : ℤ) : ℝ) := by
      have hπ : π ≠ 0 := pi_ne_zero
      push_cast
      field_simp
      ring
    rw [e, qpeAmp_add_int]
  have hI : Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  have hI' : Complex.exp ((-(π / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    rw [Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  rw [hD, hI, hI']
  ring

/-- B3 (PHASE2_SPEC.md §A.4 (3)) — for every `GroverData` (`M = 2ⁿ` included):
`phaseDist gp m y = ½ (qpeProb m (θ/π) y.toNat + qpeProb m (−θ/π) y.toNat)`. -/
theorem phaseDist_eq (gp : GroverData) (m : ℕ) (y : Reg m) :
    phaseDist gp m y =
      (qpeProb m (gp.θ / π) y.toNat + qpeProb m (-gp.θ / π) y.toNat) / 2 := by
  unfold phaseDist
  simp_rw [U_count_zero_apply_eq, phase_symm, search_symm]
  have hq : qpeProb m (gp.θ / π) y.toNat + qpeProb m (-gp.θ / π) y.toNat =
      ‖qpeAmp m (gp.θ / π - y.toNat / 2 ^ m)‖ ^ 2 +
        ‖qpeAmp m (-gp.θ / π - y.toNat / 2 ^ m)‖ ^ 2 := by
    simp only [qpeProb, Int.cast_natCast]
  rw [hq, ← norm_sq_ampA_add_ampB]
  rcases gp.psiBad_dot_self with hb | hb
  · exact sum_norm_sq_combo gp _ _ hb
  · rw [ampB_eq_zero_of_psiBad gp m y.toNat hb, hb]
    simp only [Pi.zero_apply, mul_zero, add_zero, norm_zero, zero_pow (two_ne_zero)]
    exact sum_norm_sq_good gp _

/-! ## B4 — the bound -/

theorem phaseDist_nonneg (gp : GroverData) (m : ℕ) (y : Reg m) : 0 ≤ phaseDist gp m y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

open Classical in
/-- `qpe_near_sum_ge` reindexed to `Reg m` through `toNat`. -/
theorem near_sum_ge_reg {m : ℕ} (hm : 1 ≤ m) (φ : ℝ) :
    8 / π ^ 2 ≤ ∑ y ∈ Finset.univ.filter (fun y : Reg m => CircleNear m φ y.toNat),
      qpeProb m φ y.toNat := by
  have h := qpe_near_sum_ge hm φ
  rw [Finset.sum_filter] at h ⊢
  rw [Reg.sum_toNat m (fun k : ℕ => if CircleNear m φ k then qpeProb m φ k else 0)]
  exact h

open Classical in
/-- B4 (PHASE2_SPEC.md §A.4 (4)) — for `m ≥ 1`, the outcomes near `θ/π` or near `−θ/π` on the
circle carry probability at least `8/π²`. -/
theorem qpe_two_phase_bound (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) :
    8 / π ^ 2 ≤ ∑ y ∈ Finset.univ.filter (fun y : Reg m =>
        CircleNear m (gp.θ / π) y.toNat ∨ CircleNear m (-gp.θ / π) y.toNat), phaseDist gp m y := by
  have h1 := near_sum_ge_reg hm (gp.θ / π)
  have h2 := near_sum_ge_reg hm (-gp.θ / π)
  have h3 : ∑ y ∈ Finset.univ.filter (fun y : Reg m => CircleNear m (gp.θ / π) y.toNat),
      qpeProb m (gp.θ / π) y.toNat ≤
      ∑ y ∈ Finset.univ.filter (fun y : Reg m =>
        CircleNear m (gp.θ / π) y.toNat ∨ CircleNear m (-gp.θ / π) y.toNat),
        qpeProb m (gp.θ / π) y.toNat :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.monotone_filter_right _ fun y _ h => Or.inl h) (fun y _ _ => qpeProb_nonneg _ _ _)
  have h4 : ∑ y ∈ Finset.univ.filter (fun y : Reg m => CircleNear m (-gp.θ / π) y.toNat),
      qpeProb m (-gp.θ / π) y.toNat ≤
      ∑ y ∈ Finset.univ.filter (fun y : Reg m =>
        CircleNear m (gp.θ / π) y.toNat ∨ CircleNear m (-gp.θ / π) y.toNat),
        qpeProb m (-gp.θ / π) y.toNat :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.monotone_filter_right _ fun y _ h => Or.inr h) (fun y _ _ => qpeProb_nonneg _ _ _)
  have h5 : ∑ y ∈ Finset.univ.filter (fun y : Reg m =>
        CircleNear m (gp.θ / π) y.toNat ∨ CircleNear m (-gp.θ / π) y.toNat), phaseDist gp m y =
      (∑ y ∈ Finset.univ.filter (fun y : Reg m =>
          CircleNear m (gp.θ / π) y.toNat ∨ CircleNear m (-gp.θ / π) y.toNat),
          qpeProb m (gp.θ / π) y.toNat +
        ∑ y ∈ Finset.univ.filter (fun y : Reg m =>
          CircleNear m (gp.θ / π) y.toNat ∨ CircleNear m (-gp.θ / π) y.toNat),
          qpeProb m (-gp.θ / π) y.toNat) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun y _ => phaseDist_eq gp m y
  rw [h5]
  linarith

open Classical in
/-- B4 (PHASE2_SPEC.md §A.4 (4)) — **the QPE success bound of the counting circuit**: for
`m ≥ 1`, the outcomes whose decoding `sin²(π y/2^m)` is within `ae_eps (M/2ⁿ) m` of `a = M/2ⁿ`
carry probability at least `8/π²` (`qpe_two_phase_bound`, `decode_close`, `sin_θ_eq`). The form
Stage 20b works from. -/
theorem qpe_success (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) :
    8 / π ^ 2 ≤ ∑ y ∈ Finset.univ.filter (fun y : Reg m =>
        |Real.sin (π * y.toNat / 2 ^ m) ^ 2 - gp.M / 2 ^ gp.n| ≤ ae_eps (gp.M / 2 ^ gp.n) m),
      phaseDist gp m y := by
  have ha : Real.sin gp.θ ^ 2 = gp.M / 2 ^ gp.n := by
    rw [gp.sin_θ_eq, Real.sq_sqrt (by positivity)]
  refine (qpe_two_phase_bound gp hm).trans
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun y _ _ => phaseDist_nonneg gp m y))
  refine Finset.monotone_filter_right _ fun y _ h => ?_
  have hd := decode_close gp.θ_mem (m := m) (y := (y.toNat : ℤ)) h
  rw [ha] at hd
  simpa [Int.cast_natCast] using hd

end CQRV.Grover

end
