module

import CQRV.Circuit.MBUGeneral
meta import CQRV.Circuit.MBUGeneral

/-!
# Tests for `CQRV.Circuit.MBUGeneral` (Stage 22a; PHASE2_SPEC §B.1; report §6.2.2, §6.2.4)

The axiom lines of `mbu_general`, `mbu_general_phase` and `mbu_channel_correct_of_general` (the
standard three), the §6.2.2 listing as an instance of `mbuUncompute`, the basis states `e_t(b)`,
and **the linear instance**: `f = x0 ⊕ x1`, `B = [CNOT x0 t, CNOT x1 t]`, `O = [Z x0, Z x1]`, whose
`AncRestore` conclusion `phaseOracle (x0 ⊕ x1)` follows from `mbu_general_phase`. The degree-3
instance is not here: under `Circuit.WF` an `ifBit` wraps a Clifford gate only (`Gate.bitOk`), so a
CCZ correction cannot be a well-formed circuit of this IR (docs/DECISIONS.md, Stage 22a).
-/

namespace CQRV.Tests.MBUGeneral

open CQRV CQRV.Synthesis Matrix
open scoped Kronecker

/-- info: 'CQRV.mbu_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mbu_general

/-- info: 'CQRV.mbu_general_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mbu_general_phase

/-- info: 'CQRV.mbu_channel_correct_of_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mbu_channel_correct_of_general

-- The §6.2.2 listing is `mbuUncompute` with `O = [CZ a b]`.
#guard UncomputeTempLogicalAND (.data 0) (.data 1) (.anc 0) 0 ==
  mbuUncompute (.anc 0) 0 [.cz (.data 0) (.data 1)]

-- `e_{anc 1}(b)` on three ancillae.
#guard (ancBasis 3 (.anc 1) true : Reg 3) == ![false, true, false]
#guard (ancBasis 3 (.anc 1) false : Reg 3) == ![false, false, false]

/-- `mbuCircuit` is the AND compute block, `Z t`, and the MBU uncompute. -/
example : mbuCircuit.gates = TempLogicalAND (.data 0) (.data 1) (.anc 0) ++ [.z (.anc 0)] ++
    mbuUncompute (.anc 0) 0 [.cz (.data 0) (.data 1)] := rfl

/-! ## The linear instance `f = x0 ⊕ x1` -/

/-- The parity of two data bits. -/
def parity (x : Reg 2) : Bool := xor (x 0) (x 1)

/-- `[CNOT x0 t, CNOT x1 t]` computes the parity into `t = anc 0`, phase 1. -/
theorem cnot_cnot_computesInto :
    ComputesInto 2 1 [.cnot (.data 0) (.anc 0), .cnot (.data 1) (.anc 0)] (.anc 0) parity
      (fun _ => 1) where
  unitary := by decide
  norm _ := by simp
  denote x := by
    have hanc : ∃ i, i < 1 ∧ (Qubit.anc 0) = .anc i := ⟨0, by norm_num, rfl⟩
    have h01 : Qubit.data 0 ≠ Qubit.anc 0 := by decide
    have h11 : Qubit.data 1 ≠ Qubit.anc 0 := by decide
    rw [unitaryDenote_cons_mulVec, unitaryDenote_cons_mulVec, unitaryDenote_nil, Matrix.one_mulVec,
      ← ancBasis_false 1 (.anc 0), gateU_cnot_mulVec_basisVec 2 1 h01, cnotPerm,
      get_data (n := 2) (a := 1) 0 (by norm_num), flip_ancBasis hanc]
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [gateU_cnot_mulVec_basisVec 2 1 h11, cnotPerm, get_data (n := 2) (a := 1) 1 (by norm_num),
        flip_ancBasis hanc, parity, h0, h1, Fin.zero_eta, Fin.mk_one]

/-- `[Z x0, Z x1]` is a phase implementation of the parity. -/
theorem z_z_phaseImpl : PhaseImpl 2 1 [.z (.data 0), .z (.data 1)] parity where
  unitary := by decide
  dataOnly := by decide
  phase := ⟨1, by simp, by
    rw [one_smul]
    simp only [unitaryDenote, gateU_z_data 2 1 0 (by norm_num), gateU_z_data 2 1 1 (by norm_num),
      Matrix.one_mul, ← Matrix.mul_kronecker_mul, phaseDiag_mul]
    congr 1
    congr 1
    funext x
    simp [parity, Fin.zero_eta, Fin.mk_one, Bool.xor_comm]⟩

/-- The linear instance: compute the parity into `anc 0`, `Z`, MBU uncompute with `[Z x0, Z x1]`;
the circuit applies `phaseOracle parity` and restores the ancilla. -/
example (C : Circuit) (hWF : C.WF)
    (hg : C.gates = [.cnot (.data 0) (.anc 0), .cnot (.data 1) (.anc 0)] ++ [.z (.anc 0)] ++
      mbuUncompute (.anc 0) 0 [.z (.data 0), .z (.data 1)]) :
    AncRestore 2 1 C (phaseOracle parity) :=
  mbu_general_phase_one hWF hg ⟨0, by norm_num, rfl⟩ cnot_cnot_computesInto z_z_phaseImpl

/-- The linear circuit itself: well formed, so the instance applies to it. -/
def parityCircuit : Circuit :=
  ⟨2, [.cnot (.data 0) (.anc 0), .cnot (.data 1) (.anc 0)] ++ [.z (.anc 0)] ++
    mbuUncompute (.anc 0) 0 [.z (.data 0), .z (.data 1)]⟩

#guard parityCircuit.wf

example : AncRestore 2 1 parityCircuit (phaseOracle parity) :=
  mbu_general_phase_one (by decide) rfl ⟨0, by norm_num, rfl⟩ cnot_cnot_computesInto z_z_phaseImpl

end CQRV.Tests.MBUGeneral
