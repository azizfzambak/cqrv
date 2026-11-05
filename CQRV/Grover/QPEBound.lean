module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# CQRV.Grover.QPEBound

PHASE2_SPEC.md §A.4, "Amendments before Stage 20a" (3)–(4); report §2.2, §8.2;
docs/tasks/STAGE20A_TASK.md A1–A4 (Stage 20a1) — **the analysis behind the QPE bound of the
counting circuit**: real and complex analysis only, no register and no circuit. The module imports
Mathlib only (no Physlib) and is not in the `cqr` closure.

* A1 — `qpeAmp m δ = 2^{−m} ∑_{k<2^m} e^{2πi k δ}` and `qpeProb m φ y = ‖qpeAmp m (φ − y/2^m)‖²`
  with the outcome `y : ℤ`, so that periodicity is a statement (`qpeAmp_add_int`,
  `qpeProb_add_two_pow`, `qpeProb_emod`); `qpeAmp_zero`; the closed form `qpeProb_closed`
  (`geom_sum_eq` and `‖e^{ix} − 1‖ = 2 |sin (x/2)|`).
* A2 — `two_point_bound : 8 ≤ sin²(πt) (1/t² + 1/(1−t)²)` for `0 < t < 1`, equality at `t = ½`.
  Route: `t ≤ ½` by symmetry; on `(0, ¼]` concavity of `sin` between `0` and `π/4` gives
  `sin (πt) ≥ 2√2 t`; on `[¼, ½]`, with `s = ½ − t` and `q = s² ≤ 1/16`, `sin (πt) = cos (πs) ≥
  1 − (π²/2) q ≥ 1 − 4.97 q > 0` (`one_sub_sq_div_two_le_cos`, `π < 3.15`) and the polynomial
  inequality `(1 − 4q)² ≤ (1 − 4.97 q)² (1 + 4q)`. (The two simpler bounds one tries first are
  false at `t = ¼`: `sin (πt) ≥ 4t(1−t)`, and `sinc t + sinc (1−t) ≥ 4/π`; the harness shows it.)
* A3 — `qpeProb_two_neighbours`: the outcomes `⌊2^m φ⌋` and `⌊2^m φ⌋ + 1` carry probability
  `≥ 8/π²`; `CircleNear m φ y := ∃ z : ℤ, |y/2^m − φ − z| ≤ 2^{−m}` (the circle distance `≤ 2^{−m}`
  without a new distance) and `qpe_near_sum_ge` (`m ≥ 1`: the two neighbours are distinct mod
  `2^m`).
* A4 — `ae_eps a m = 2π √(a(1−a))/2^m + π²/4^m`, `sin_sq_sub_le`, and `decode_close`: an outcome
  near `θ/π` or `−θ/π` decodes to `sin²(π y/2^m)` within `ae_eps (sin²θ) m` of `sin²θ`.
-/

@[expose] public section

namespace CQRV.Grover

open Real

/-! ## A1 — the amplitude and the probability -/

/-- PHASE2_SPEC.md §A.4 (3) — the QPE amplitude at offset `δ`: `2^{−m} ∑_{k<2^m} e^{2πi k δ}`. -/
noncomputable def qpeAmp (m : ℕ) (δ : ℝ) : ℂ :=
  ((2 ^ m : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 ^ m), Complex.exp (2 * π * Complex.I * k * δ)

/-- PHASE2_SPEC.md §A.4 (3) — the QPE outcome distribution of a phase `φ`: the probability of
the integer outcome `y` (read modulo `2^m`). -/
noncomputable def qpeProb (m : ℕ) (φ : ℝ) (y : ℤ) : ℝ := ‖qpeAmp m (φ - y / 2 ^ m)‖ ^ 2

/-- The amplitude has period 1 in the offset. -/
theorem qpeAmp_add_int (m : ℕ) (δ : ℝ) (z : ℤ) : qpeAmp m (δ + z) = qpeAmp m δ := by
  unfold qpeAmp
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : (2 * π * Complex.I * k * ((δ + z : ℝ) : ℂ)) =
      2 * π * Complex.I * k * δ + (((k : ℤ) * z : ℤ) : ℂ) * (2 * π * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem qpeProb_add_int_mul (m : ℕ) (φ : ℝ) (y z : ℤ) :
    qpeProb m φ (y + z * 2 ^ m) = qpeProb m φ y := by
  unfold qpeProb
  have hN : (2 : ℝ) ^ m ≠ 0 := by positivity
  have h : φ - ((y + z * 2 ^ m : ℤ) : ℝ) / 2 ^ m = (φ - y / 2 ^ m) + ((-z : ℤ) : ℝ) := by
    push_cast
    rw [add_div, mul_div_cancel_right₀ _ hN]
    ring
  rw [h, qpeAmp_add_int]

/-- The distribution has period `2^m` in the outcome. -/
theorem qpeProb_add_two_pow (m : ℕ) (φ : ℝ) (y : ℤ) :
    qpeProb m φ (y + 2 ^ m) = qpeProb m φ y := by
  have h := qpeProb_add_int_mul m φ y 1
  rwa [one_mul] at h

/-- `qpeProb` depends on the outcome only through `y % 2^m`. -/
theorem qpeProb_emod (m : ℕ) (φ : ℝ) (y : ℤ) : qpeProb m φ (y % 2 ^ m) = qpeProb m φ y := by
  have h := qpeProb_add_int_mul m φ (y % 2 ^ m) (y / 2 ^ m)
  rw [mul_comm, Int.emod_add_mul_ediv] at h
  exact h.symm

theorem qpeAmp_zero (m : ℕ) : qpeAmp m 0 = 1 := by
  have hN : ((2 ^ m : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_pos (by norm_num : (0 : ℕ) < 2) m).ne'
  simp only [qpeAmp, Complex.ofReal_zero, mul_zero, Complex.exp_zero, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ hN

theorem qpeProb_nonneg (m : ℕ) (φ : ℝ) (y : ℤ) : 0 ≤ qpeProb m φ y := sq_nonneg _

theorem norm_exp_sub_one_sq (x : ℝ) :
    ‖Complex.exp (Complex.I * x) - 1‖ ^ 2 = 4 * Real.sin (x / 2) ^ 2 := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, sq_abs]
  ring

/-- A1 — the closed form of the QPE probability: `sin²(π 2^m δ) / (2^m sin (π δ))²`. -/
theorem qpeProb_closed (m : ℕ) (δ : ℝ) (h : Real.sin (π * δ) ≠ 0) :
    ‖qpeAmp m δ‖ ^ 2 = Real.sin (π * 2 ^ m * δ) ^ 2 / ((2 ^ m) ^ 2 * Real.sin (π * δ) ^ 2) := by
  have hterm : ∀ k : ℕ, Complex.exp (2 * π * Complex.I * k * δ) =
      Complex.exp (Complex.I * ((2 * π * δ : ℝ) : ℂ)) ^ k := by
    intro k
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hw1 : ‖Complex.exp (Complex.I * ((2 * π * δ : ℝ) : ℂ)) - 1‖ ^ 2 =
      4 * Real.sin (π * δ) ^ 2 := by
    rw [norm_exp_sub_one_sq]
    congr 3
    ring
  have hne : Complex.exp (Complex.I * ((2 * π * δ : ℝ) : ℂ)) ≠ 1 := by
    intro e
    rw [e, sub_self, norm_zero] at hw1
    have h0 : Real.sin (π * δ) ^ 2 = 0 := by linarith
    exact h (pow_eq_zero_iff (two_ne_zero) |>.mp h0)
  have hwN : ‖Complex.exp (Complex.I * ((2 * π * δ : ℝ) : ℂ)) ^ 2 ^ m - 1‖ ^ 2 =
      4 * Real.sin (π * 2 ^ m * δ) ^ 2 := by
    have e : Complex.exp (Complex.I * ((2 * π * δ : ℝ) : ℂ)) ^ 2 ^ m =
        Complex.exp (Complex.I * ((2 ^ m * (2 * π * δ) : ℝ) : ℂ)) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e, norm_exp_sub_one_sq]
    congr 3
    ring
  have hs : Real.sin (π * δ) ^ 2 ≠ 0 := pow_ne_zero 2 h
  unfold qpeAmp
  simp_rw [hterm]
  rw [geom_sum_eq hne, norm_mul, norm_inv, norm_div, Complex.norm_natCast, mul_pow, inv_pow,
    div_pow, hwN, hw1]
  push_cast
  field_simp

/-! ## A2 — the inequality -/

/-- A2 on `(0, ¼]`: concavity of `sin` between `0` and `π/4` gives `sin (πt) ≥ 2√2 t`. -/
theorem two_point_bound_small {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1 / 4) :
    8 ≤ Real.sin (π * t) ^ 2 * (1 / t ^ 2 + 1 / (1 - t) ^ 2) := by
  have hsin : 2 * Real.sqrt 2 * t ≤ Real.sin (π * t) := by
    have hc := strictConcaveOn_sin_Icc.concaveOn
    have h0mem : (0 : ℝ) ∈ Set.Icc 0 π := ⟨le_rfl, pi_pos.le⟩
    have h4mem : π / 4 ∈ Set.Icc 0 π := ⟨by positivity, by linarith [pi_pos]⟩
    have h := hc.2 h0mem h4mem (by linarith : (0 : ℝ) ≤ 1 - 4 * t) (by linarith : (0 : ℝ) ≤ 4 * t)
      (by ring)
    simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add, Real.sin_pi_div_four] at h
    rw [show 4 * t * (π / 4) = π * t by ring] at h
    linarith
  have hpos : 0 ≤ 2 * Real.sqrt 2 * t := by positivity
  have h8 : 8 * t ^ 2 ≤ Real.sin (π * t) ^ 2 := by
    have h := pow_le_pow_left₀ hpos hsin 2
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have e : (2 * Real.sqrt 2 * t) ^ 2 = 8 * t ^ 2 := by
      rw [mul_pow, mul_pow, hs]
      ring
    rw [e] at h
    exact h
  have ht2 : 0 < t ^ 2 := by positivity
  have ha : 8 ≤ Real.sin (π * t) ^ 2 * (1 / t ^ 2) := by
    rw [mul_one_div, le_div_iff₀ ht2]
    exact h8
  have hb : 0 ≤ Real.sin (π * t) ^ 2 * (1 / (1 - t) ^ 2) := by positivity
  rw [mul_add]
  linarith

/-- A2 on `[¼, ½]`: with `s = ½ − t`, `sin (πt) = cos (πs) ≥ 1 − 4.97 s²` and a polynomial
inequality in `q = s² ≤ 1/16`. -/
theorem two_point_bound_mid {t : ℝ} (h0 : 1 / 4 ≤ t) (h1 : t ≤ 1 / 2) :
    8 ≤ Real.sin (π * t) ^ 2 * (1 / t ^ 2 + 1 / (1 - t) ^ 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = 1 / 2 - s := ⟨1 / 2 - t, by ring⟩
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 / 4 := by linarith
  have hq0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hq1 : s ^ 2 ≤ 1 / 16 := by nlinarith
  have hsin : Real.sin (π * (1 / 2 - s)) = Real.cos (π * s) := by
    rw [show π * (1 / 2 - s) = π / 2 - π * s by ring, Real.sin_pi_div_two_sub]
  have hpi2 : π ^ 2 ≤ 9.9225 := by
    have h := Real.pi_lt_d2
    nlinarith [pi_pos]
  have hcos : 1 - 497 / 100 * s ^ 2 ≤ Real.cos (π * s) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := π * s)
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hpi2)]
  have hL : 0 ≤ 1 - 497 / 100 * s ^ 2 := by linarith
  have hc2 : (1 - 497 / 100 * s ^ 2) ^ 2 ≤ Real.cos (π * s) ^ 2 := pow_le_pow_left₀ hL hcos 2
  have hpoly : (1 - 4 * s ^ 2) ^ 2 ≤ (1 - 497 / 100 * s ^ 2) ^ 2 * (1 + 4 * s ^ 2) := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1), pow_nonneg hq0 3, hq0]
  have hkey : (1 - 4 * s ^ 2) ^ 2 ≤ Real.cos (π * s) ^ 2 * (1 + 4 * s ^ 2) :=
    hpoly.trans (mul_le_mul_of_nonneg_right hc2 (by positivity))
  have hu : (1 / 2 - s) ≠ 0 := by linarith
  have hv : (1 / 2 + s) ≠ 0 := by linarith
  have hd : 0 < 1 / 4 - s ^ 2 := by linarith
  have hsum : 1 / (1 / 2 - s) ^ 2 + 1 / (1 - (1 / 2 - s)) ^ 2 =
      (1 / 2 + 2 * s ^ 2) / (1 / 4 - s ^ 2) ^ 2 := by
    rw [show 1 - (1 / 2 - s) = 1 / 2 + s by ring,
      show (1 / 4 - s ^ 2) = (1 / 2 - s) * (1 / 2 + s) by ring,
      div_add_div _ _ (pow_ne_zero 2 hu) (pow_ne_zero 2 hv), mul_pow]
    congr 1
    ring
  rw [hsin, hsum, mul_div_assoc', le_div_iff₀ (pow_pos hd 2)]
  nlinarith [hkey]

/-- A2 (PHASE2_SPEC.md §A.4 (4)) — `8 ≤ sin²(πt) (1/t² + 1/(1−t)²)` on `(0, 1)`; equality at
`t = ½`. -/
theorem two_point_bound {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    8 ≤ Real.sin (π * t) ^ 2 * (1 / t ^ 2 + 1 / (1 - t) ^ 2) := by
  have half : ∀ {u : ℝ}, 0 < u → u ≤ 1 / 2 →
      8 ≤ Real.sin (π * u) ^ 2 * (1 / u ^ 2 + 1 / (1 - u) ^ 2) := by
    intro u hu0 hu1
    rcases le_total u (1 / 4) with h | h
    · exact two_point_bound_small hu0 h
    · exact two_point_bound_mid h hu1
  rcases le_total t (1 / 2) with h | h
  · exact half h0 h
  · have h' := half (u := 1 - t) (by linarith) (by linarith)
    rw [show π * (1 - t) = π - π * t by ring, Real.sin_pi_sub, sub_sub_cancel, add_comm] at h'
    exact h'

/-! ## A3 — the two neighbours and the near set -/

/-- The QPE probability at offset `δ` is at least `sinc²` of `2^m δ`. -/
theorem sin_sq_div_le_qpe (m : ℕ) {δ : ℝ} (h : Real.sin (π * δ) ≠ 0) :
    Real.sin (π * 2 ^ m * δ) ^ 2 / (π * 2 ^ m * δ) ^ 2 ≤ ‖qpeAmp m δ‖ ^ 2 := by
  rw [qpeProb_closed m δ h]
  have hs : 0 < Real.sin (π * δ) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 h).symm
  have h2 : (0 : ℝ) < (2 ^ m) ^ 2 := by positivity
  refine div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos h2 hs) ?_
  calc ((2 : ℝ) ^ m) ^ 2 * Real.sin (π * δ) ^ 2
      ≤ ((2 : ℝ) ^ m) ^ 2 * (π * δ) ^ 2 := mul_le_mul_of_nonneg_left Real.sin_sq_le_sq h2.le
    _ = (π * 2 ^ m * δ) ^ 2 := by ring

/-- A3 (PHASE2_SPEC.md §A.4 (4)) — the two outcomes next to `2^m φ` carry probability at least
`8/π²`. -/
theorem qpeProb_two_neighbours (m : ℕ) (φ : ℝ) :
    8 / π ^ 2 ≤ qpeProb m φ ⌊2 ^ m * φ⌋ + qpeProb m φ (⌊2 ^ m * φ⌋ + 1) := by
  have hN0 : (0 : ℝ) < 2 ^ m := by positivity
  have hN1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hf1 := Int.floor_le ((2 : ℝ) ^ m * φ)
  have hf2 := Int.lt_floor_add_one ((2 : ℝ) ^ m * φ)
  generalize ⌊(2 : ℝ) ^ m * φ⌋ = F at hf1 hf2 ⊢
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 ^ m * φ - F := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t < 1 := by linarith
  have hδ1 : φ - (F : ℝ) / 2 ^ m = t / 2 ^ m := by
    rw [ht, sub_div, mul_div_cancel_left₀ _ hN0.ne']
  have hδ2 : φ - ((F + 1 : ℤ) : ℝ) / 2 ^ m = (t - 1) / 2 ^ m := by
    rw [ht]
    push_cast
    rw [sub_div, sub_div, mul_div_cancel_left₀ _ hN0.ne', add_div]
    ring
  have hpi : 8 / π ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  unfold qpeProb
  rw [hδ1, hδ2]
  rcases ht0.eq_or_lt with h0 | h0
  · rw [← h0, zero_div, qpeAmp_zero, norm_one, one_pow]
    have h2 := sq_nonneg ‖qpeAmp m ((0 - 1) / 2 ^ m)‖
    linarith
  · -- the first neighbour: `π δ₁ ∈ (0, π)`
    have hd1 : t / 2 ^ m < 1 := by
      rw [div_lt_one hN0]
      linarith
    have hs1 : Real.sin (π * (t / 2 ^ m)) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (mul_lt_of_lt_one_right pi_pos hd1)).ne'
    have b1 := sin_sq_div_le_qpe m hs1
    rw [show π * 2 ^ m * (t / 2 ^ m) = π * t by field_simp] at b1
    -- the second neighbour: `π δ₂ ∈ (−π, 0)`
    have hd2 : -1 < (t - 1) / 2 ^ m := by
      rw [lt_div_iff₀ hN0]
      linarith
    have hd2' : (t - 1) / 2 ^ m < 0 := div_neg_of_neg_of_pos (by linarith) hN0
    have hs2 : Real.sin (π * ((t - 1) / 2 ^ m)) ≠ 0 :=
      (Real.sin_neg_of_neg_of_neg_pi_lt (mul_neg_of_pos_of_neg pi_pos hd2')
        (by nlinarith [pi_pos])).ne
    have b2 := sin_sq_div_le_qpe m hs2
    rw [show π * 2 ^ m * ((t - 1) / 2 ^ m) = π * t - π by field_simp, Real.sin_sub_pi, neg_sq,
      show (π * t - π) ^ 2 = (π * (1 - t)) ^ 2 by ring] at b2
    have hA := two_point_bound h0 ht1
    have h1t : (1 - t) ≠ 0 := by linarith
    have e : Real.sin (π * t) ^ 2 / (π * t) ^ 2 + Real.sin (π * t) ^ 2 / (π * (1 - t)) ^ 2 =
        Real.sin (π * t) ^ 2 * (1 / t ^ 2 + 1 / (1 - t) ^ 2) / π ^ 2 := by
      have ht' : t ≠ 0 := h0.ne'
      have hpi' : π ≠ 0 := pi_ne_zero
      field_simp
    calc 8 / π ^ 2 ≤ Real.sin (π * t) ^ 2 * (1 / t ^ 2 + 1 / (1 - t) ^ 2) / π ^ 2 := by gcongr
      _ = Real.sin (π * t) ^ 2 / (π * t) ^ 2 + Real.sin (π * t) ^ 2 / (π * (1 - t)) ^ 2 := e.symm
      _ ≤ _ := add_le_add b1 b2

/-- PHASE2_SPEC.md §A.4 (4) — the outcome `y` is within `2^{−m}` of the phase `φ` on the circle:
`‖y/2^m − φ‖ ≤ 2^{−m}` modulo 1, without a new distance. -/
def CircleNear (m : ℕ) (φ : ℝ) (y : ℤ) : Prop := ∃ z : ℤ, |(y : ℝ) / 2 ^ m - φ - z| ≤ (2 ^ m : ℝ)⁻¹

/-- `CircleNear` passes to the representative modulo `2^m`. -/
theorem CircleNear.emod {m : ℕ} {φ : ℝ} {y : ℤ} (h : CircleNear m φ y) :
    CircleNear m φ (y % 2 ^ m) := by
  obtain ⟨z, hz⟩ := h
  refine ⟨z - y / 2 ^ m, ?_⟩
  have hN : (2 : ℝ) ^ m ≠ 0 := by positivity
  have e : ((y % 2 ^ m : ℤ) : ℝ) = y - 2 ^ m * ((y / 2 ^ m : ℤ) : ℝ) := by
    have h2 : ((y % 2 ^ m + 2 ^ m * (y / 2 ^ m) : ℤ) : ℝ) = y := by
      rw [Int.emod_add_mul_ediv]
    push_cast at h2
    linarith
  have e2 : ((y % 2 ^ m : ℤ) : ℝ) / 2 ^ m - φ - ((z - y / 2 ^ m : ℤ) : ℝ) =
      (y : ℝ) / 2 ^ m - φ - z := by
    rw [e]
    push_cast
    rw [sub_div, mul_div_cancel_left₀ _ hN]
    ring
  rw [e2]
  exact hz

/-- An integer within 1 of `2^m φ` is near `φ`. -/
theorem circleNear_of_abs_le {m : ℕ} {φ : ℝ} {y : ℤ} (h : |(y : ℝ) - 2 ^ m * φ| ≤ 1) :
    CircleNear m φ y := by
  refine ⟨0, ?_⟩
  have hN0 : (0 : ℝ) < 2 ^ m := by positivity
  have e : (y : ℝ) / 2 ^ m - φ - ((0 : ℤ) : ℝ) = ((y : ℝ) - 2 ^ m * φ) / 2 ^ m := by
    rw [Int.cast_zero, sub_zero, sub_div, mul_div_cancel_left₀ _ hN0.ne']
  rw [e, abs_div, abs_of_pos hN0, inv_eq_one_div]
  gcongr

theorem circleNear_floor (m : ℕ) (φ : ℝ) : CircleNear m φ ⌊(2 : ℝ) ^ m * φ⌋ := by
  have h1 := Int.floor_le ((2 : ℝ) ^ m * φ)
  have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ m * φ)
  exact circleNear_of_abs_le (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem circleNear_floor_add_one (m : ℕ) (φ : ℝ) : CircleNear m φ (⌊(2 : ℝ) ^ m * φ⌋ + 1) := by
  have h1 := Int.floor_le ((2 : ℝ) ^ m * φ)
  have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ m * φ)
  refine circleNear_of_abs_le (abs_le.mpr ⟨?_, ?_⟩) <;> push_cast <;> linarith

open Classical in
/-- A3 (PHASE2_SPEC.md §A.4 (4)) — for `m ≥ 1`, the outcomes `y < 2^m` near `φ` on the circle
carry probability at least `8/π²`: the two neighbours of `2^m φ`, reduced modulo `2^m`, are
distinct (the only use of `m ≥ 1`) and near. -/
theorem qpe_near_sum_ge {m : ℕ} (hm : 1 ≤ m) (φ : ℝ) :
    8 / π ^ 2 ≤
      ∑ y ∈ (Finset.range (2 ^ m)).filter (fun y : ℕ => CircleNear m φ y), qpeProb m φ y := by
  have hNpos : (0 : ℤ) < 2 ^ m := by positivity
  have hN2 : (1 : ℤ) < 2 ^ m := by
    calc (1 : ℤ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  obtain ⟨F, hF⟩ : ∃ F : ℤ, F = ⌊(2 : ℝ) ^ m * φ⌋ := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = F % 2 ^ m :=
    ⟨(F % 2 ^ m).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ hNpos.ne')⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = (F + 1) % 2 ^ m :=
    ⟨((F + 1) % 2 ^ m).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ hNpos.ne')⟩
  have halt : a < 2 ^ m := by
    have h : (a : ℤ) < 2 ^ m := ha ▸ Int.emod_lt_of_pos F hNpos
    exact_mod_cast h
  have hblt : b < 2 ^ m := by
    have h : (b : ℤ) < 2 ^ m := hb ▸ Int.emod_lt_of_pos (F + 1) hNpos
    exact_mod_cast h
  have hab : a ≠ b := by
    intro e
    have h : (F + 1) % 2 ^ m = F % 2 ^ m := by rw [← ha, ← hb, e]
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, add_sub_cancel_left,
      Int.emod_eq_of_lt (by norm_num) hN2] at h
    exact one_ne_zero h
  have hanear : CircleNear m φ (a : ℤ) := by
    rw [ha, hF]
    exact (circleNear_floor m φ).emod
  have hbnear : CircleNear m φ (b : ℤ) := by
    rw [hb, hF]
    exact (circleNear_floor_add_one m φ).emod
  have hsub : ({a, b} : Finset ℕ) ⊆
      (Finset.range (2 ^ m)).filter (fun y : ℕ => CircleNear m φ y) := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hy with rfl | rfl
    · exact ⟨halt, hanear⟩
    · exact ⟨hblt, hbnear⟩
  calc 8 / π ^ 2 ≤ qpeProb m φ F + qpeProb m φ (F + 1) := by
        rw [hF]
        exact qpeProb_two_neighbours m φ
    _ = qpeProb m φ (a : ℤ) + qpeProb m φ (b : ℤ) := by
        rw [ha, hb, qpeProb_emod, qpeProb_emod]
    _ = ∑ y ∈ ({a, b} : Finset ℕ), qpeProb m φ y :=
        (Finset.sum_pair (f := fun y : ℕ => qpeProb m φ (y : ℤ)) hab).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => qpeProb_nonneg m φ y)

/-! ## A4 — the decoding -/

/-- PHASE2_SPEC.md §A.4 — the precision of the amplitude estimate at `m` phase qubits:
`2π √(a(1−a))/2^m + π²/4^m`. -/
noncomputable def ae_eps (a : ℝ) (m : ℕ) : ℝ :=
  2 * π * Real.sqrt (a * (1 - a)) / 2 ^ m + π ^ 2 / 4 ^ m

theorem sin_sq_sub_sin_sq (θ Δ : ℝ) :
    Real.sin (θ + Δ) ^ 2 - Real.sin θ ^ 2 = Real.sin (2 * θ + Δ) * Real.sin Δ := by
  rw [Real.sin_add, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
  linear_combination (-(Real.sin Δ) ^ 2) * Real.sin_sq_add_cos_sq θ +
    (Real.sin θ) ^ 2 * Real.sin_sq_add_cos_sq Δ

/-- A4 — `|sin²(θ+Δ) − sin²θ| ≤ |sin 2θ| |Δ| + Δ²`. -/
theorem sin_sq_sub_le (θ Δ : ℝ) :
    |Real.sin (θ + Δ) ^ 2 - Real.sin θ ^ 2| ≤ |Real.sin (2 * θ)| * |Δ| + Δ ^ 2 := by
  rw [sin_sq_sub_sin_sq, abs_mul]
  have hs : |Real.sin Δ| ≤ |Δ| := Real.abs_sin_le_abs
  have h1 : |Real.sin (2 * θ + Δ)| ≤ |Real.sin (2 * θ)| + |Δ| := by
    rw [Real.sin_add]
    calc |Real.sin (2 * θ) * Real.cos Δ + Real.cos (2 * θ) * Real.sin Δ|
        ≤ |Real.sin (2 * θ) * Real.cos Δ| + |Real.cos (2 * θ) * Real.sin Δ| := abs_add_le _ _
      _ ≤ |Real.sin (2 * θ)| + |Δ| := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one Δ))
          ((mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one (2 * θ))).trans hs)
  calc |Real.sin (2 * θ + Δ)| * |Real.sin Δ|
      ≤ (|Real.sin (2 * θ)| + |Δ|) * |Δ| := mul_le_mul h1 hs (abs_nonneg _) (by positivity)
    _ = |Real.sin (2 * θ)| * |Δ| + Δ ^ 2 := by rw [add_mul, ← sq, sq_abs]

/-- The decoding bound for a phase `θ'/π` with the same `sin²` and `|sin 2·|` as `θ`. -/
theorem decode_close_aux {θ θ' : ℝ} {m : ℕ} {y : ℤ} (hsq : Real.sin θ' ^ 2 = Real.sin θ ^ 2)
    (habs : |Real.sin (2 * θ')| = |Real.sin (2 * θ)|) (h : CircleNear m (θ' / π) y) :
    |Real.sin (π * y / 2 ^ m) ^ 2 - Real.sin θ ^ 2| ≤
      |Real.sin (2 * θ)| * (π / 2 ^ m) + (π / 2 ^ m) ^ 2 := by
  obtain ⟨z, hz⟩ := h
  have hN0 : (0 : ℝ) < 2 ^ m := by positivity
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = π * ((y : ℝ) / 2 ^ m - θ' / π - z) := ⟨_, rfl⟩
  have hΔle : |Δ| ≤ π / 2 ^ m := by
    rw [hΔ, abs_mul, abs_of_pos pi_pos, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hz pi_pos.le
  have harg : π * y / 2 ^ m = (θ' + Δ) + z * π := by
    rw [hΔ]
    field_simp
    ring
  have hsin : Real.sin (π * y / 2 ^ m) ^ 2 = Real.sin (θ' + Δ) ^ 2 := by
    rw [harg, Real.sin_add_int_mul_pi, mul_pow]
    rcases Int.even_or_odd z with he | ho
    · rw [he.neg_one_zpow, one_pow, one_mul]
    · rw [ho.neg_one_zpow, neg_one_sq, one_mul]
  rw [hsin, ← hsq]
  have hΔ2 : Δ ^ 2 ≤ (π / 2 ^ m) ^ 2 := by
    rw [← sq_abs Δ]
    exact pow_le_pow_left₀ (abs_nonneg _) hΔle 2
  have hmul := mul_le_mul_of_nonneg_left hΔle (abs_nonneg (Real.sin (2 * θ')))
  have hmain := sin_sq_sub_le θ' Δ
  rw [← habs]
  linarith

/-- A4 (PHASE2_SPEC.md §A.4 (4)) — an outcome near `θ/π` or near `−θ/π` on the circle decodes to
`sin²(π y/2^m)` within `ae_eps (sin²θ) m` of `sin²θ`; the same bound for both signs. -/
theorem decode_close {θ : ℝ} (hθ : 0 ≤ θ ∧ θ ≤ π / 2) {m : ℕ} {y : ℤ}
    (h : CircleNear m (θ / π) y ∨ CircleNear m (-θ / π) y) :
    |Real.sin (π * y / 2 ^ m) ^ 2 - Real.sin θ ^ 2| ≤ ae_eps (Real.sin θ ^ 2) m := by
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hθ.2⟩
  have hsqrt : Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) = Real.sin θ * Real.cos θ := by
    rw [← Real.cos_sq', ← mul_pow, Real.sqrt_sq (mul_nonneg hs hc)]
  have h2 : |Real.sin (2 * θ)| = 2 * (Real.sin θ * Real.cos θ) := by
    rw [Real.sin_two_mul, abs_of_nonneg (by positivity)]
    ring
  have h4 : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hbound : |Real.sin (2 * θ)| * (π / 2 ^ m) + (π / 2 ^ m) ^ 2 =
      ae_eps (Real.sin θ ^ 2) m := by
    rw [ae_eps, hsqrt, h2, div_pow, h4]
    ring
  rw [← hbound]
  rcases h with h | h
  · exact decode_close_aux rfl rfl h
  · exact decode_close_aux (θ' := -θ) (by rw [Real.sin_neg, neg_sq])
      (by rw [mul_neg, Real.sin_neg, abs_neg]) h

end CQRV.Grover

end
