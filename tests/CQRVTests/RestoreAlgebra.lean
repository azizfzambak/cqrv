module

import CQRV.Circuit.RestoreAlgebra
meta import CQRV.Circuit.RestoreAlgebra

/-!
# Tests for `CQRV.Circuit.RestoreAlgebra` (Stage 23a; PHASE2_SPEC §B.2; report §6.2.1, §6.2.4)

The axiom lines of `ancRestore_list`, `ancRestoreMix_of_kraus`, `mbu_uncorrected`,
`AncRestore.widen` and `AncRestore.comp_widen` (the standard three); `mbu_uncorrected` at the AND
(`mbuCircuit` without its `CZ`, and without its `Z` and `CZ`); `AncRestore.widen` on the 22a linear
instance, from one to two ancillae; a two-block list: the AND oracle of `mbuCircuit` followed by the
parity instance; `comp_widen` of the two on two ancillae.
-/

namespace CQRV.Tests.RestoreAlgebra

open CQRV CQRV.Synthesis Matrix
open scoped MState

/-- info: 'CQRV.ancRestore_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ancRestore_list

/-- info: 'CQRV.ancRestoreMix_of_kraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ancRestoreMix_of_kraus

/-- info: 'CQRV.mbu_uncorrected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mbu_uncorrected

/-- info: 'CQRV.AncRestore.widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AncRestore.widen

/-- info: 'CQRV.AncRestore.comp_widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AncRestore.comp_widen

/-! ## MBU without its correction at the AND -/

/-- `mbuCircuit` without its `CZ`: compute, `Z t`, `H t`, measure, reset. -/
def mbuNoCorr : Circuit :=
  ⟨2, TempLogicalAND (.data 0) (.data 1) (.anc 0) ++ [.z (.anc 0)] ++ mbuUncompute (.anc 0) 0 []⟩

/-- `mbuCircuit` without its `Z` and its `CZ`: compute, `H t`, measure, reset. -/
def mbuNoCorr' : Circuit :=
  ⟨2, TempLogicalAND (.data 0) (.data 1) (.anc 0) ++ mbuUncompute (.anc 0) 0 []⟩

#guard mbuNoCorr.wf
#guard mbuNoCorr'.wf

/-- The AND gadget without its correction dephases the controls in the basis of `x0 ∧ x1`. -/
example (ρ : MState (Reg 2)) :
    (channelDenote 2 1 mbuNoCorr (ρ ⊗ᴹ ancZero 1)).m =
      (1 / 2 : ℂ) • (ρ ⊗ᴹ ancZero 1).m + (1 / 2 : ℂ) • ((czU ◃ ρ) ⊗ᴹ ancZero 1).m :=
  mbu_uncorrected_phase (C := mbuNoCorr) (by decide) rfl ⟨0, by norm_num, rfl⟩
    tempLogicalAND_computesInto ρ

example (ρ : MState (Reg 2)) :
    (channelDenote 2 1 mbuNoCorr' (ρ ⊗ᴹ ancZero 1)).m =
      (1 / 2 : ℂ) • (ρ ⊗ᴹ ancZero 1).m + (1 / 2 : ℂ) • ((czU ◃ ρ) ⊗ᴹ ancZero 1).m :=
  mbu_uncorrected (C := mbuNoCorr') (by decide) rfl ⟨0, by norm_num, rfl⟩
    tempLogicalAND_computesInto ρ

/-! ## The 22a linear instance (restated: test modules export nothing) -/

/-- The parity of two data bits. -/
def parity (x : Reg 2) : Bool := xor (x 0) (x 1)

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

/-- The linear circuit of 22a. -/
def parityCircuit : Circuit :=
  ⟨2, [.cnot (.data 0) (.anc 0), .cnot (.data 1) (.anc 0)] ++ [.z (.anc 0)] ++
    mbuUncompute (.anc 0) 0 [.z (.data 0), .z (.data 1)]⟩

theorem parityCircuit_restores : AncRestore 2 1 parityCircuit (phaseOracle parity) :=
  mbu_general_phase_one (by decide) rfl ⟨0, by norm_num, rfl⟩ cnot_cnot_computesInto z_z_phaseImpl

/-! ## Widening and block lists -/

#guard ancsBelow parityCircuit.gates 1
#guard ancsBelow mbuCircuit.gates 1
#guard !ancsBelow parityCircuit.gates 0

/-- `AncRestore.widen` on the linear instance: from one ancilla to two. -/
example : AncRestore 2 (1 + 1) parityCircuit (phaseOracle parity) :=
  parityCircuit_restores.widen (by decide) (by decide)

/-- A two-block list: the AND oracle of `mbuCircuit`, then the parity instance. -/
example : AncRestore 2 1 (mbuCircuit.append parityCircuit) (phaseOracle parity * czU) :=
  (ancRestore_list [(parityCircuit, phaseOracle parity)]
    (fun p hp => by
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨by decide, parityCircuit_restores⟩)
    mbuCircuit czU (by decide) mbu_channel_correct).2

/-- The same two blocks, each certified on one ancilla, composed on two ancillae. -/
example : AncRestore 2 2 (mbuCircuit.append parityCircuit) (phaseOracle parity * czU) :=
  AncRestore.comp_widen (a₁ := 1) (a₂ := 1) mbuCircuit_WF (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num) mbu_channel_correct parityCircuit_restores

end CQRV.Tests.RestoreAlgebra
