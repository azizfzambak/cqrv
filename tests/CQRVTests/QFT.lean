module

import CQRV.Synthesis.QFT
import CQRV.Circuit.QFTCorrect
meta import CQRV.Synthesis.QFT
meta import CQRV.Circuit.QFTCorrect

/-!
# QFT and approximate QFT (Stage 18b, PHASE2_SPEC.md §A.2; docs/tasks/STAGE18_TASK.md B5)

The gate lists written out for `m = 3`, the measured grades of `qftCircuit m` for `m = 1..8` and
of `aqftCircuit 6 kmax` for `kmax = 1..6` (`t = 0`, `tDepth = 0`, `rot = twoQ = m (m − 1) / 2`,
`meas = ff = 0`, `d` as measured), the encodings on hand-written registers (qubit 0 the most
significant bit, as the harness), `example` instances of the theorems of B2 / B3 at `m = 3`, and
the axiom lines of `qft_basis` and `qftCircuit_WF`.
-/

namespace CQRV.Tests.QFT

open CQRV CQRV.Synthesis Matrix

/-! ## Gate lists -/

#guard qftGates 3 == [.h (.data 0), .cp 1 2 (.data 1) (.data 0), .cp 1 3 (.data 2) (.data 0),
  .h (.data 1), .cp 1 2 (.data 2) (.data 1), .h (.data 2)]

-- `k ≥ 2` always: `kmax = 1` keeps the Hadamards only
#guard aqftGates 3 1 == [.h (.data 0), .h (.data 1), .h (.data 2)]
#guard aqftGates 3 2 == [.h (.data 0), .cp 1 2 (.data 1) (.data 0), .h (.data 1),
  .cp 1 2 (.data 2) (.data 1), .h (.data 2)]
#guard aqftGates 3 3 == qftGates 3

-- the inverse QFT (§A.0.1): the adjoint gates in reverse order, `cp (-1) k`
#guard adjointGates (qftGates 3) == [.h (.data 2), .cp (-1) 2 (.data 2) (.data 1), .h (.data 1),
  .cp (-1) 3 (.data 2) (.data 0), .cp (-1) 2 (.data 1) (.data 0), .h (.data 0)]

#guard (List.range 8).all fun i => (qftGates (i + 1)).length == (i + 1) * (i + 2) / 2
#guard (List.range 8).all fun i => (qftCircuit (i + 1)).wf
#guard (List.range 8).all fun i => (qftGates (i + 1)).all Gate.isUnitary

/-! ## Measured grades (`Circuit.grade` / `Circuit.gradeExt`, the decision-4 schedule) -/

#guard (qftCircuit 1).grade = ⟨1, 1, 0, 0⟩ ∧ (qftCircuit 1).gradeExt = ⟨0, 0, 0, 0, 0⟩
#guard (qftCircuit 2).grade = ⟨2, 3, 0, 0⟩ ∧ (qftCircuit 2).gradeExt = ⟨1, 0, 1, 0, 0⟩
#guard (qftCircuit 3).grade = ⟨3, 5, 0, 0⟩ ∧ (qftCircuit 3).gradeExt = ⟨3, 0, 3, 0, 0⟩
#guard (qftCircuit 4).grade = ⟨4, 7, 0, 0⟩ ∧ (qftCircuit 4).gradeExt = ⟨6, 0, 6, 0, 0⟩
#guard (qftCircuit 5).grade = ⟨5, 9, 0, 0⟩ ∧ (qftCircuit 5).gradeExt = ⟨10, 0, 10, 0, 0⟩
#guard (qftCircuit 6).grade = ⟨6, 11, 0, 0⟩ ∧ (qftCircuit 6).gradeExt = ⟨15, 0, 15, 0, 0⟩
#guard (qftCircuit 7).grade = ⟨7, 13, 0, 0⟩ ∧ (qftCircuit 7).gradeExt = ⟨21, 0, 21, 0, 0⟩
#guard (qftCircuit 8).grade = ⟨8, 15, 0, 0⟩ ∧ (qftCircuit 8).gradeExt = ⟨28, 0, 28, 0, 0⟩

-- `aqftCircuit 6 kmax`: `kmax = 1` is six parallel Hadamards (depth 1); from `kmax = 2` on the
-- depth is that of the full QFT (the chain through qubit 0's `cp 1 2` and the last Hadamards)
#guard (aqftCircuit 6 1).grade = ⟨6, 1, 0, 0⟩ ∧ (aqftCircuit 6 1).gradeExt = ⟨0, 0, 0, 0, 0⟩
#guard (aqftCircuit 6 2).grade = ⟨6, 11, 0, 0⟩ ∧ (aqftCircuit 6 2).gradeExt = ⟨5, 0, 5, 0, 0⟩
#guard (aqftCircuit 6 3).grade = ⟨6, 11, 0, 0⟩ ∧ (aqftCircuit 6 3).gradeExt = ⟨9, 0, 9, 0, 0⟩
#guard (aqftCircuit 6 4).grade = ⟨6, 11, 0, 0⟩ ∧ (aqftCircuit 6 4).gradeExt = ⟨12, 0, 12, 0, 0⟩
#guard (aqftCircuit 6 5).grade = ⟨6, 11, 0, 0⟩ ∧ (aqftCircuit 6 5).gradeExt = ⟨14, 0, 14, 0, 0⟩
#guard (aqftCircuit 6 6).grade = ⟨6, 11, 0, 0⟩ ∧ (aqftCircuit 6 6).gradeExt = ⟨15, 0, 15, 0, 0⟩
#guard (List.range 6).map (fun k => (aqftGates 6 (k + 1)).length) == [6, 11, 15, 18, 20, 21]

/-! ## Encodings (qubit 0 the most significant bit) -/

#guard Reg.toNat (![true, false, true] : Reg 3) = 5
#guard Reg.toNatLE (![true, false, true] : Reg 3) = 5
#guard Reg.toNat (![true, true, false] : Reg 3) = 6
#guard Reg.toNatLE (![true, true, false] : Reg 3) = 3
#guard Reg.toNat (bitRev (![true, true, false] : Reg 3)) = 3
#guard (List.finRange 3).map (fun j => Reg.ofNat 3 6 j) == [true, true, false]
#guard (List.range 8).all fun x => (Reg.ofNat 3 x).toNat == x
#guard (List.range 8).all fun x => (Reg.ofNat 3 x).toNat % 2 ^ (3 - 1) == x % 4
#guard Reg.bit (![true, false, true] : Reg 3) 2 = true
#guard Reg.bit (![true, false, true] : Reg 3) 3 = false
#guard reg0 == (fun i => i.elim0)

/-! ## The theorems at `m = 3` -/

example (s : Reg 3) : s.toNat < 8 := Reg.toNat_lt s
example (s : Reg 3) : Reg.ofNat 3 s.toNat = s := Reg.ofNat_toNat s
example (x : ℕ) (hx : x < 8) : (Reg.ofNat 3 x).toNat = x := Reg.toNat_ofNat hx
example : Function.Injective (Reg.toNat (m := 3)) := Reg.toNat_injective
example (s : Reg 3) : (bitRev s).toNat = s.toNatLE := Reg.toNat_bitRev s
example (s : Reg 3) : bitRev (bitRev s) = s := bitRev_bitRev s
example (s : Reg 3) (j : ℕ) :
    s.toNat % 2 ^ (3 - j) = ∑ i : Fin 3, if j ≤ (i : ℕ) ∧ s i then 2 ^ (3 - 1 - (i : ℕ)) else 0 :=
  Reg.toNat_mod s j
example (s : Reg 3) : s.toNat % 2 ^ (3 - 1) =
    ∑ l ∈ Finset.Ico 1 3, if s.bit l then 2 ^ (3 - 1 - l) else 0 :=
  Reg.toNat_mod_eq_sum_Ico s (by norm_num)

example : (qftCircuit 3).WF := qftCircuit_WF 3
example : (aqftCircuit 3 2).WF := aqftCircuit_WF 3 2
example : ∀ g ∈ qftGates 3, g.isUnitary = true := qftGates_unitary 3
example : (qftGates 3).length = 6 := qftGates_length 3
example : aqftGates 3 5 = qftGates 3 := aqftGates_eq_self (by norm_num)
example : unitaryDenote 3 0 (aqftGates 3 3) = unitaryDenote 3 0 (qftGates 3) :=
  aqft_eq_qft_of_le le_rfl
example : unitaryDenote 3 0 (qftGates 3) ∈ Matrix.unitaryGroup (Reg 3 × Reg 0) ℂ := qft_unitary 3

example (x : Reg 3) (hj : 1 < 3) :
    (if x.bit 1 then (-1 : ℂ) else 1) *
        ∏ i ∈ Finset.range (3 - 1 - 1), (if x.bit (1 + i + 1) then phaseOf 1 (i + 2) else 1) =
      qftExp 3 1 x :=
  exp_phase_block x hj

example (x s : Reg 3) :
    (unitaryDenote 3 0 (qftGates 3) *ᵥ basisVec (x, reg0)) (s, reg0) =
      ((Real.sqrt 2)⁻¹ : ℂ) ^ 3 *
        Complex.exp (2 * Real.pi * Complex.I * ((x.toNat * (bitRev s).toNat : ℕ) : ℂ) / 2 ^ 3) :=
  qft_basis 3 x s

/-! ## Axioms -/

/-- info: 'CQRV.qft_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qft_basis

/-- info: 'CQRV.exp_sum_phases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_sum_phases

/-- info: 'CQRV.qftCircuit_WF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qftCircuit_WF

end CQRV.Tests.QFT
