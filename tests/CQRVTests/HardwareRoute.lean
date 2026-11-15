module

import CQRV.Hardware.Route
meta import CQRV.Hardware.Route

/-!
# Tests for `CQRV.Hardware.Relabel` / `Route` (Stage 26b1; PHASE2_SPEC §C.3 step 2; report §5.3, §9.1.1)

The axiom lines of `channelDenote_relabel`, `ud_swapEntry`, `channelDenote_embed` and
`nAnc_translate`; the MBU gadget relabeled, placed and laid out as a physical circuit on the compact
register (well formed, the right qubits, by `decide`); the transfer of `mbu_channel_correct` to that
physical circuit through `channelDenote_embed`; the counterexample to the general ancilla-count
statement and its corrected form on the gadget.
-/

namespace CQRV.Tests.HardwareRoute

open CQRV CQRV.Hardware
open scoped MState

/-- info: 'CQRV.Hardware.channelDenote_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms channelDenote_relabel

/-- info: 'CQRV.Hardware.ud_swapEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ud_swapEntry

/-- info: 'CQRV.Hardware.channelDenote_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms channelDenote_embed

/-- info: 'CQRV.Hardware.nAnc_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nAnc_translate

/-! ## The gadget on a physical register of five qubits

Two data qubits, one ancilla, two idle qubits; the layout `σ` sends the canonical positions
`0, 1, 2` (x0, x1, a0) to the physical qubits `3, 1, 4`: `σ = swap 0 3 ∘ swap 2 4` on `Fin 5`. -/

def σ5 : Equiv.Perm (Fin 5) := (Equiv.swap 2 4).trans (Equiv.swap 0 3)

def physGadget : Circuit := physOf (n := 2) (a := 1) 2 σ5 mbuCircuit

#guard physGadget.nData == 5
#guard physGadget.wf
#guard physGadget.gates.length == mbuCircuit.gates.length
-- every qubit is a data qubit of the compact register; x0 ↦ 3, x1 ↦ 1, a0 ↦ 4
#guard (physGadget.gates.flatMap Gate.qubits).all (fun q => match q with | .data i => i < 5 | .anc _ => false)
#guard physGadget.gates.head? == some (.h (.data 4))
#guard (physGadget.gates.filter (fun g => match g with | .ifBit _ _ => true | _ => false))
  == [.ifBit 0 (.cz (.data 3) (.data 1)), .ifBit 0 (.x (.data 4))]
#guard (physGadget.gates.filter (fun g => match g with | .measure _ _ => true | _ => false)) == [.measure (.data 4) 0]

/-- The transfer of `mbu_channel_correct`: on the embedded clean input the physical gadget outputs
the embedded `CZ` output (PHASE2_SPEC §C.3, `AncRestore.phys` at this instance). -/
theorem physGadget_correct (ρ : MState (Reg 2)) :
    channelDenote 5 0 physGadget (embed 2 σ5 (ρ ⊗ᴹ ancZero 1)) = embed 2 σ5 ((czU ◃ ρ) ⊗ᴹ ancZero 1) := by
  have h := channelDenote_embed (n := 2) (a := 1) 2 σ5 mbuCircuit mbuCircuit_WF (by decide) (by decide)
    (ρ ⊗ᴹ ancZero 1)
  rw [mbu_channel_correct] at h
  exact h

/-! ## The ancilla count -/

/-- The general statement `(translateCircuit b C).nAnc = C.nAnc` is false: an ancilla that is only
allocated vanishes with the bookkeeping. -/
def lonelyAlloc : Circuit := ⟨1, [.alloc (.anc 3)]⟩

#guard lonelyAlloc.nAnc == 4
#guard (translateCircuit .cz lonelyAlloc).nAnc == 0
#guard lonelyAlloc.ancCovered == false
-- the gadget's ancilla is covered, and the count is kept (the theorem's hypothesis, decided)
#guard mbuCircuit.ancCovered
#guard (translateCircuit .cz mbuCircuit).nAnc == mbuCircuit.nAnc

example : (translateCircuit .cx mbuCircuit).nAnc = mbuCircuit.nAnc := nAnc_translate .cx mbuCircuit (by decide)

/-! ## The SWAP entry's phase -/

#guard (swapEntry .cz (.data 0) (.data 1)).irPhase == 3 / 4
#guard (swapEntry .cx (.data 0) (.data 1)).irPhase == 0

end CQRV.Tests.HardwareRoute
