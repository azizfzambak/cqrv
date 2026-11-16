module

public import CQRV.Hardware.CheckSound
public import CQRVTests.HardwareWitnessSound
meta import CQRV.Hardware.CheckSound
meta import CQRVTests.HardwareWitnessSound

/-!
# Tests for `CQRV.Hardware.Check` / `CheckSound` (Stage 26c1 L1–L3; PHASE2_SPEC §C.3; report §9.1.1)

The axiom lines of `applyWitnessQ_ok`, `layOf_layPerm` and `embed_zero`; the linear check on the
gadget artifact decided by the kernel and equal to the artifact's physical circuit; two tampered
witnesses refused; the layout permutation on the gadget's layout and on a layout with an idle qubit;
the coupling check on the gadget against FakeTorino's edges among its used qubits, and a gate off
the edges refused.
-/

namespace CQRV.Tests.HardwareCheck

open CQRV CQRV.Hardware CQRV.Tests.HardwareWitness CQRV.Tests.HardwareWitnessSound
open scoped MState

/-- info: 'CQRV.Hardware.applyWitnessQ_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms applyWitnessQ_ok

/-- info: 'CQRV.Hardware.layOf_layPerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms layOf_layPerm

/-- info: 'CQRV.Hardware.embed_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms embed_zero

/-! ## L1: the linear check on the gadget -/

set_option maxRecDepth 100000 in
/-- The linear check reconstructs the artifact's physical circuit, by the kernel. -/
theorem gadget_applyWitnessQ : applyWitnessQ .cz mbuCircuit gadgetW 3 = .ok gadgetPhys := by rfl

/-- Through `applyWitnessQ_ok`, the reconstruction of 26b2 holds for the gadget. -/
theorem gadget_applyWitness' : applyWitness .cz mbuCircuit gadgetW 3 = .ok gadgetPhys :=
  applyWitnessQ_ok .cz mbuCircuit mbuCircuit_WF gadgetW 3 gadgetPhys gadget_applyWitnessQ

-- an element taken twice, and a changed final layout, are refused
#guard (applyWitnessQ .cz mbuCircuit { gadgetW with order := gadgetW.order ++ [.elem 0] } 3).toOption == none
#guard (applyWitnessQ .cz mbuCircuit { gadgetW with final := [0, 1, 2] } 3).toOption == none
-- an element out of its queue order (element 1 before element 0, both on the same qubit) is refused
#guard (applyWitnessQ .cz mbuCircuit { gadgetW with order := .elem 1 :: .elem 0 :: gadgetW.order.drop 2 } 3).toOption == none

/-! ## L2: the layout permutation -/

example : IsLayout 3 3 [1, 0, 2] := by decide
example : layOf 3 3 (layPerm 3 3 [1, 0, 2]) = [1, 0, 2] := layOf_layPerm 3 3 _ (by decide)
-- a layout with an idle qubit: three logical positions on a register of four
example : layOf 4 3 (layPerm 4 3 [3, 0, 2]) = [3, 0, 2] := layOf_layPerm 4 3 _ (by decide)
-- the gadget's initial layout is `swap 0 1` (26b3) and also `layPerm 3 3 [1, 0, 2]`
example : gadgetW.initial = layOf 3 3 (layPerm 3 3 [1, 0, 2]) := (layOf_layPerm 3 3 _ (by decide)).symm

/-! ## L3: the coupling check -/

/-- FakeTorino's coupling-map edges among the gadget's used qubits 54, 60, 61
(`hw/targets/fake_torino.json`, both orientations as the file states them). -/
def torinoEdgesGadget : List (ℕ × ℕ) := [(54, 61), (60, 61), (61, 54), (61, 60)]

#guard edgesOk gadgetPhys [54, 60, 61] torinoEdgesGadget
-- compact qubits 0 and 1 (device 54 and 60) are not an edge
#guard !edgesOk (gadgetPhys ++ [.cz (.data 0) (.data 1)]) [54, 60, 61] torinoEdgesGadget
#guard !edgesOk [.ifBit 0 (.cz (.data 0) (.data 1))] [54, 60, 61] torinoEdgesGadget
-- the two-qubit gates of the gadget's physical circuit
#guard (twoQubitPairs gadgetPhys).length == 13

end CQRV.Tests.HardwareCheck
