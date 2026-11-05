module

import CQRV.Grover.QPEBound

/-!
# The analysis behind the QPE bound (Stage 20a1, PHASE2_SPEC.md §A.4 "Amendments before Stage 20a";
docs/tasks/STAGE20A_TASK.md A1–A5)

`example` instances of the theorems of `CQRV.Grover.QPEBound` at `m = 1, 2` — the amplitude and
its periodicity, the closed form, the inequality `two_point_bound` at `t = ½` (where it is an
equality) and `t = ¼`, the two neighbours, the near set, the decoding — and the axiom lines of
`two_point_bound`, `qpeProb_two_neighbours`, `qpe_near_sum_ge`, `decode_close`. No real number can
be `#guard`ed; the numerical checks are part (f) of `tests/diff/counting_diff.py`.
-/

namespace CQRV.Tests.QPEBound

open CQRV.Grover Real

/-! ## A1 — the amplitude and the probability -/

example : qpeAmp 1 0 = 1 := qpeAmp_zero 1
example : qpeAmp 2 0 = 1 := qpeAmp_zero 2
example (δ : ℝ) : qpeAmp 2 (δ + (3 : ℤ)) = qpeAmp 2 δ := qpeAmp_add_int 2 δ 3
example (φ : ℝ) (y : ℤ) : qpeProb 2 φ (y + 2 ^ 2) = qpeProb 2 φ y := qpeProb_add_two_pow 2 φ y
example (φ : ℝ) : qpeProb 1 φ (5 % 2 ^ 1) = qpeProb 1 φ 5 := qpeProb_emod 1 φ 5
example (φ : ℝ) (y : ℤ) : 0 ≤ qpeProb 2 φ y := qpeProb_nonneg 2 φ y
example (δ : ℝ) (h : Real.sin (π * δ) ≠ 0) :
    ‖qpeAmp 2 δ‖ ^ 2 = Real.sin (π * 2 ^ 2 * δ) ^ 2 / ((2 ^ 2) ^ 2 * Real.sin (π * δ) ^ 2) :=
  qpeProb_closed 2 δ h

/-! ## A2 — the inequality, at `t = ½` (attained) and `t = ¼` -/

example : 8 ≤ Real.sin (π * (1 / 2)) ^ 2 * (1 / (1 / 2 : ℝ) ^ 2 + 1 / (1 - 1 / 2) ^ 2) :=
  two_point_bound (by norm_num) (by norm_num)
example : Real.sin (π * (1 / 2)) ^ 2 * (1 / (1 / 2 : ℝ) ^ 2 + 1 / (1 - 1 / 2) ^ 2) = 8 := by
  rw [show π * (1 / 2) = π / 2 by ring, Real.sin_pi_div_two]
  norm_num
example : 8 ≤ Real.sin (π * (1 / 4)) ^ 2 * (1 / (1 / 4 : ℝ) ^ 2 + 1 / (1 - 1 / 4) ^ 2) :=
  two_point_bound (by norm_num) (by norm_num)

/-! ## A3 — the two neighbours and the near set -/

example (φ : ℝ) :
    8 / π ^ 2 ≤ qpeProb 1 φ ⌊(2 : ℝ) ^ 1 * φ⌋ + qpeProb 1 φ (⌊(2 : ℝ) ^ 1 * φ⌋ + 1) :=
  qpeProb_two_neighbours 1 φ
example (φ : ℝ) :
    8 / π ^ 2 ≤ qpeProb 2 φ ⌊(2 : ℝ) ^ 2 * φ⌋ + qpeProb 2 φ (⌊(2 : ℝ) ^ 2 * φ⌋ + 1) :=
  qpeProb_two_neighbours 2 φ

example : CircleNear 2 (1 / 4) 1 := ⟨0, by norm_num⟩
example (φ : ℝ) : CircleNear 2 φ ⌊(2 : ℝ) ^ 2 * φ⌋ := circleNear_floor 2 φ
example (φ : ℝ) (y : ℤ) (h : CircleNear 2 φ y) : CircleNear 2 φ (y % 2 ^ 2) := h.emod

open Classical in
example (φ : ℝ) :
    8 / π ^ 2 ≤
      ∑ y ∈ (Finset.range (2 ^ 1)).filter (fun y : ℕ => CircleNear 1 φ y), qpeProb 1 φ y :=
  qpe_near_sum_ge (le_refl 1) φ

open Classical in
example (φ : ℝ) :
    8 / π ^ 2 ≤
      ∑ y ∈ (Finset.range (2 ^ 2)).filter (fun y : ℕ => CircleNear 2 φ y), qpeProb 2 φ y :=
  qpe_near_sum_ge (by norm_num) φ

/-! ## A4 — the decoding -/

example (θ Δ : ℝ) :
    |Real.sin (θ + Δ) ^ 2 - Real.sin θ ^ 2| ≤ |Real.sin (2 * θ)| * |Δ| + Δ ^ 2 :=
  sin_sq_sub_le θ Δ
example (a : ℝ) : ae_eps a 2 = 2 * π * Real.sqrt (a * (1 - a)) / 2 ^ 2 + π ^ 2 / 4 ^ 2 := rfl
example {θ : ℝ} (hθ : 0 ≤ θ ∧ θ ≤ π / 2) {y : ℤ} (h : CircleNear 2 (θ / π) y) :
    |Real.sin (π * y / 2 ^ 2) ^ 2 - Real.sin θ ^ 2| ≤ ae_eps (Real.sin θ ^ 2) 2 :=
  decode_close hθ (Or.inl h)
example {θ : ℝ} (hθ : 0 ≤ θ ∧ θ ≤ π / 2) {y : ℤ} (h : CircleNear 1 (-θ / π) y) :
    |Real.sin (π * y / 2 ^ 1) ^ 2 - Real.sin θ ^ 2| ≤ ae_eps (Real.sin θ ^ 2) 1 :=
  decode_close hθ (Or.inr h)

/-! ## Axioms (CLAUDE.md rule 10) -/

/-- info: 'CQRV.Grover.two_point_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_point_bound

/-- info: 'CQRV.Grover.qpeProb_two_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qpeProb_two_neighbours

/-- info: 'CQRV.Grover.qpe_near_sum_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qpe_near_sum_ge

/-- info: 'CQRV.Grover.decode_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decode_close

end CQRV.Tests.QPEBound
