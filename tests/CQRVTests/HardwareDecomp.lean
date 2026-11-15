module

import CQRV.Hardware.DecompSound
meta import CQRV.Hardware.DecompSound

/-!
# Tests for `CQRV.Hardware.Decomp` / `DecompSound` (Stage 26a; PHASE2_SPEC §C.3; report §5.3, §9.1.1)

The axiom lines of `decomp_sound` and `translate_sound`; `translate` and `translateCircuit` on the
MBU gadget in both bases (its gate counts, well-formedness, classical bits, and that the expanded
circuit is Clifford-conditioned); the transfer of `mbu_channel_correct` to the translated gadget as
an example of `translate_channel`; the embedding phases and the two phase conventions on `h`.
-/

namespace CQRV.Tests.HardwareDecomp

open CQRV CQRV.Hardware
open scoped MState

/-- info: 'CQRV.Hardware.decomp_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decomp_sound

/-- info: 'CQRV.Hardware.translate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms translate_sound

/-- info: 'CQRV.Hardware.realizes_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms realizes_translate

/-! ## The translation of the MBU gadget -/

-- the cz basis: 3 h (3 basis gates each), 2 t, 2 tdg, 1 s, 1 z, 6 cnot (7 each), the measurement,
-- the conditioned cz (1) and x (1)
#guard (translate .cz mbuCircuit).length == 60
-- the cx basis: cnot is 1 basis gate, the conditioned cz is h cx h (7)
#guard (translate .cx mbuCircuit).length == 30
#guard (translateCircuit .cz mbuCircuit).wf
#guard (translateCircuit .cx mbuCircuit).wf
#guard (translateCircuit .cz mbuCircuit).nBits == mbuCircuit.nBits
#guard (translateCircuit .cz mbuCircuit).nAnc == mbuCircuit.nAnc
#guard (translateCircuit .cx mbuCircuit).nAnc == mbuCircuit.nAnc
-- the conditioned part: `ifBit 0 (cz x0 x1)` stays one conditioned `cz` in the cz basis
#guard (translate .cz mbuCircuit).filter (fun g => match g with | .ifBit _ _ => true | _ => false)
  == [.ifBit 0 (.cz (.data 0) (.data 1)), .ifBit 0 (.x (.anc 0))]
-- and becomes seven conditioned basis gates in the cx basis, all Clifford after expansion
#guard ((translate .cx mbuCircuit).filter (fun g => match g with | .ifBit _ _ => true | _ => false)).length == 8
#guard ((translateCircuit .cx mbuCircuit).gates.filter (fun g => match g with | .ifBit _ _ => true | _ => false)).all
  (fun g => match g with | .ifBit _ g' => g'.isClifford | _ => false)

/-! ## The phases -/

#guard (decompTable .cz (.h (.data 0))).phase == -1 / 8
#guard (decompTable .cz (.h (.data 0))).irPhase == 1 / 8
#guard (decompTable .cz (.cnot (.data 0) (.data 1))).phase == -1 / 4
#guard (decompTable .cz (.cnot (.data 0) (.data 1))).irPhase == 1 / 4
#guard (decompTable .cx (.cnot (.data 0) (.data 1))).irPhase == 0
#guard (pEntry 3 5 (.data 0)).phase == -3 / 64
#guard (pEntry 3 5 (.data 0)).irPhase == 0
#guard (cpEntry .cz 1 1 (.data 0) (.data 1)).irPhase == 1 / 2
#guard (cpEntry .cx 1 1 (.data 0) (.data 1)).irPhase == 0
#guard (swapEntry .cz (.data 0) (.data 1)).phase == -3 / 4

/-! ## The transfer: `mbu_channel_correct` on the translated gadget -/

/-- Report §6.2.2 — the translated MBU gadget has the channel of the gadget, hence restores its
ancilla and applies `CZ` (`translate_channel` on `mbu_channel_correct`). -/
theorem mbu_translate_correct (b : TargetBasis) (ρ : MState (Reg 2)) :
    channelDenote 2 1 (translateCircuit b mbuCircuit) (ρ ⊗ᴹ ancZero 1) = (czU ◃ ρ) ⊗ᴹ ancZero 1 := by
  rw [translate_channel 2 1 b mbuCircuit mbuCircuit_WF (by decide) (by decide)]
  exact mbu_channel_correct ρ

/-- The same, as `AncRestore` through `AncRestore.translate`. -/
theorem mbu_translate_restores (b : TargetBasis) :
    AncRestore 2 1 (translateCircuit b mbuCircuit) czU :=
  AncRestore.translate 2 1 b mbuCircuit_WF (by decide) (by decide) mbu_channel_correct

end CQRV.Tests.HardwareDecomp
