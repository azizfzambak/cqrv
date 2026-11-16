module

public import CQRV.Hardware.WitnessSound
public import CQRVTests.HardwareWitness
meta import CQRV.Hardware.WitnessSound
meta import CQRVTests.HardwareWitness

/-!
# Tests for `CQRV.Hardware.WitnessSound` (Stage 26b3; PHASE2_SPEC §C.3 step 3; report §9.1.1)

The axiom lines of `applyWitness_sound`, `AncRestore.phys`, `realizes_phys`; the MBU gadget
artifact's witness as a Lean literal (the compact register of its three used qubits), its
reconstruction equal to the artifact's physical circuit **by `decide`** (the kernel evaluates
`applyWitness`), and `gadgetPhys_correct`: `mbu_channel_correct` transferred to the artifact's
physical circuit through `applyWitness_sound` — not through 26b1's hand placement.
-/

namespace CQRV.Tests.HardwareWitnessSound

open CQRV CQRV.Hardware CQRV.Tests.HardwareWitness
open scoped MState

@[expose] public section

/-- info: 'CQRV.Hardware.applyWitness_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms applyWitness_sound

/-- info: 'CQRV.Hardware.AncRestore.phys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AncRestore.phys

/-- info: 'CQRV.Hardware.realizes_phys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms realizes_phys

/-! ## The gadget artifact's witness, as data -/

/-- `hw/artifacts/mbu_gadget__fake_torino/witness.json` on the compact register
(used qubits 54, 60, 61 ↦ 0, 1, 2); the same witness `Witness.ofJson` reads in
`CQRV.Tests.HardwareWitness`. -/
def gadgetW : Witness :=
  { basis := .cz, nLogical := 3, initial := [1, 0, 2], final := [1, 0, 2],
    order := [.elem 0, .elem 1, .elem 2, .elem 3, .elem 4, .elem 5, .elem 6, .elem 7, .elem 18, .elem 19,
      .elem 20, .elem 8, .elem 9, .elem 10, .elem 11, .elem 12, .elem 13, .elem 14, .elem 25, .elem 26,
      .elem 27, .elem 15, .elem 16, .elem 17, .elem 21, .elem 22, .elem 23, .elem 24, .elem 32, .elem 35,
      .elem 36, .elem 37, .elem 28, .elem 29, .elem 30, .elem 31, .elem 33, .elem 42, .elem 43, .elem 44,
      .elem 34, .elem 38, .elem 39, .elem 40, .elem 41, .elem 45, .elem 46, .elem 47, .elem 48, .elem 49,
      .elem 50, .elem 51, .elem 52, .elem 53, .elem 54, .elem 55, .elem 56, .elem 57, .elem 58, .elem 59],
    blocks := [(58, [.swap 2 1, .gate 58, .swap 2 1]), (59, [.gate 59])],
    clbitMap := [0], seed := 0 }

-- the literal is the parsed witness, field by field
#guard gadgetWitness?.map (·.initial) == some gadgetW.initial
#guard gadgetWitness?.map (·.final) == some gadgetW.final
#guard gadgetWitness?.map (·.order) == some gadgetW.order
#guard gadgetWitness?.map (·.blocks) == some gadgetW.blocks

/-- The initial layout `[1, 0, 2]` as a permutation of the compact register: `swap 0 1`. -/
def σ₀ : Equiv.Perm (Fin 3) := Equiv.swap 0 1

theorem gadget_initial : gadgetW.initial = layOf 3 3 σ₀ := by decide

set_option maxRecDepth 100000 in
/-- **The reconstruction equals the artifact's physical circuit, by the kernel** (`rfl`: the kernel
evaluates `applyWitness` on the witness and the circuit). -/
theorem gadget_applyWitness : applyWitness .cz mbuCircuit gadgetW 3 = .ok gadgetPhys := by rfl

set_option maxRecDepth 100000 in
theorem gadgetPhys_WF : (physCircuit 3 gadgetPhys).WF := by decide +kernel

theorem gadgetPhys_nBits : (physCircuit 3 gadgetPhys).nBits = mbuCircuit.nBits := by decide

/-- The gadget: two data qubits, one ancilla, no idle qubit (`bb = 0`), so the physical register is
`2 + (1 + 0) = 3` and the final layout determines `σ_f`. -/
theorem layOf_full_inj (σ τ : Equiv.Perm (Fin 3)) (h : layOf 3 3 σ = layOf 3 3 τ) : σ = τ := by
  ext x
  have := congrArg (fun l => l.getD x.val 0) h
  simp only [layOf_getD _ _ x.isLt, permFn_lt _ x.isLt] at this
  simpa using this

set_option maxRecDepth 8000 in
/-- **`gadgetPhys_correct`** (PHASE2_SPEC §C.3, X4): `mbu_channel_correct` transferred to the
artifact's physical circuit through `applyWitness_sound` — on the embedded clean input, laid out by
the witness's initial layout, the reconstructed physical gadget gives the embedded `CZ` output at the
witness's final layout (the same layout: the block's SWAPs cancel). -/
theorem gadgetPhys_correct (ρ : MState (Reg 2)) :
    channelDenote 3 0 (physCircuit 3 gadgetPhys) (embed 0 σ₀ (ρ ⊗ᴹ ancZero 1)) =
      embed 0 σ₀ ((czU ◃ ρ) ⊗ᴹ ancZero 1) := by
  obtain ⟨σf, hf, h⟩ := AncRestore.phys .cz mbuCircuit gadgetW 0 mbuCircuit_WF gadgetPhys gadget_applyWitness
    gadgetPhys_WF gadgetPhys_nBits σ₀ gadget_initial (U := czU) mbu_channel_correct
  have hσ : σf = σ₀ := layOf_full_inj σf σ₀ (hf.symm.trans gadget_initial)
  have h' := h ρ
  rw [hσ] at h'
  exact h'

/-- info: 'CQRV.Tests.HardwareWitnessSound.gadgetPhys_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gadgetPhys_correct

end

end CQRV.Tests.HardwareWitnessSound
