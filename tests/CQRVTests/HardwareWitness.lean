module

import CQRV.Hardware.Reorder
meta import CQRV.Hardware.Reorder

/-!
# Tests for `CQRV.Hardware.Witness` / `Reorder` (Stage 26b2; PHASE2_SPEC §C.3 steps 2–3; report §9.1.1)

The axiom lines of `gateK_comm_of_disjoint`, `krausOps_reorder` and `krausOps_swap_migrate`; the
dependency-queue reordering on small lists; the MBU gadget artifact's witness
(`hw/artifacts/mbu_gadget__fake_torino/witness.json`, inline, compacted to its three used qubits)
read by `Witness.ofJson`, and `applyWitness` on it equal, gate for gate, to the artifact's physical
circuit (`hw/transpile.py`'s `expand_swaps`, exported on the compact register), by evaluation.
-/

namespace CQRV.Tests.HardwareWitness

open CQRV CQRV.Hardware

/-- info: 'CQRV.Hardware.gateK_comm_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gateK_comm_of_disjoint

/-- info: 'CQRV.Hardware.krausOps_reorder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms krausOps_reorder

/-- info: 'CQRV.Hardware.krausOps_swap_migrate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms krausOps_swap_migrate

/-! ## The dependency queues -/

def g0 : Gate := .h (.data 0)
def g1 : Gate := .x (.data 1)
def g2 : Gate := .cnot (.data 0) (.data 1)
def m0 : Gate := .measure (.data 0) 0
def c1 : Gate := .ifBit 0 (.x (.data 1))

-- independent gates may be exchanged; dependent ones may not
#guard validReorder Gate.qubits Gate.bits [g0, g1] [g1, g0]
#guard validReorder Gate.qubits Gate.bits [g0, g1, g2] [g1, g0, g2]
#guard !validReorder Gate.qubits Gate.bits [g0, g2] [g2, g0]
-- a measurement and the gate it conditions share a classical bit, even on disjoint qubits
#guard !validReorder Gate.qubits Gate.bits [m0, c1] [c1, m0]
#guard validReorder Gate.qubits Gate.bits [m0, g1] [g1, m0]
-- every element exactly once
#guard !validReorder Gate.qubits Gate.bits [g0, g1] [g0]
#guard !validReorder Gate.qubits Gate.bits [g0] [g0, g0]
#guard splitFirst g1 [g0, g1, g2] == some ([g0], [g2])

/-! ## The MBU gadget artifact -/

/-- `hw/artifacts/mbu_gadget__fake_torino/witness.json`. -/
def gadgetWitnessText : String := r#"{"basis":"cz","blocks":{"58":[{"swap":[61,60]},{"g":58},{"swap":[61,60]}],"59":[{"g":59}]},"clbit_map":[0],"entries_used":["cnot","cz","h","measure","s","t","tdg","x","z"],"final_layout":[60,54,61],"initial_layout":[60,54,61],"n_logical":3,"order":[{"e":0},{"e":1},{"e":2},{"e":3},{"e":4},{"e":5},{"e":6},{"e":7},{"e":18},{"e":19},{"e":20},{"e":8},{"e":9},{"e":10},{"e":11},{"e":12},{"e":13},{"e":14},{"e":25},{"e":26},{"e":27},{"e":15},{"e":16},{"e":17},{"e":21},{"e":22},{"e":23},{"e":24},{"e":32},{"e":35},{"e":36},{"e":37},{"e":28},{"e":29},{"e":30},{"e":31},{"e":33},{"e":42},{"e":43},{"e":44},{"e":34},{"e":38},{"e":39},{"e":40},{"e":41},{"e":45},{"e":46},{"e":47},{"e":48},{"e":49},{"e":50},{"e":51},{"e":52},{"e":53},{"e":54},{"e":55},{"e":56},{"e":57},{"e":58},{"e":59}],"schema_version":"1.0.0","seed":0,"swaps":2,"target":"fake_torino","versions":{"passes":"SabreLayout(coupling_map, seed) alone in a PassManager (qiskit 2.6.2)","qiskit":"2.6.2","qiskit_aer":"0.18.2","qiskit_ibm_runtime":"0.52.1","transpile_py":"hw/transpile.py (Stage 25a)"}}"#

/-- The manifest's `layout.used_qubits`: the compact register has three qubits. -/
def gadgetUsed : List ℕ := [54, 60, 61]

def gadgetWitness? : Option Witness :=
  (Lean.Json.parse gadgetWitnessText >>= fun j => Witness.ofJson j gadgetUsed).toOption

#guard gadgetWitness?.isSome
#guard gadgetWitness?.map (·.initial) == some [1, 0, 2]
#guard gadgetWitness?.map (·.final) == some [1, 0, 2]
#guard gadgetWitness?.map (·.order.length) == some 60
#guard gadgetWitness?.map (·.blocks.length) == some 2
#guard (elements .cz mbuCircuit).length == 60
#guard (translate .cz mbuCircuit).length == 60

/-- The artifact's physical circuit on the compact register (used qubits 54, 60, 61 ↦ 0, 1, 2), as
`hw/transpile.py` produces it (`expand_swaps` of the routed circuit), 102 basis gates. -/
def gadgetPhys : List BasisGate := [
  .rz (1) 2 (.data 2),
  .sx (.data 2),
  .rz (1) 2 (.data 2),
  .rz (1) 3 (.data 2),
  .rz (1) 2 (.data 2),
  .sx (.data 2),
  .rz (1) 2 (.data 2),
  .cz (.data 1) (.data 2),
  .rz (1) 2 (.data 1),
  .sx (.data 1),
  .rz (1) 2 (.data 1),
  .rz (1) 2 (.data 2),
  .sx (.data 2),
  .rz (1) 2 (.data 2),
  .rz (1) 2 (.data 2),
  .sx (.data 2),
  .rz (1) 2 (.data 2),
  .cz (.data 0) (.data 2),
  .rz (1) 2 (.data 0),
  .sx (.data 0),
  .rz (1) 2 (.data 0),
  .rz (1) 2 (.data 2),
  .sx (.data 2),
  .rz (1) 2 (.data 2),
  .cz (.data 2) (.data 1),
  .rz (1) 2 (.data 1),
  .sx (.data 1),
  .rz (1) 2 (.data 1),
  .rz (-1) 3 (.data 1),
  .rz (1) 2 (.data 1),
  .sx (.data 1),
  .rz (1) 2 (.data 1),
  .cz (.data 2) (.data 0),
  .rz (1) 2 (.data 0),
  .sx (.data 0),
  .rz (1) 2 (.data 0),
  .rz (-1) 3 (.data 0),
  .rz (1) 2 (.data 0),
  .sx (.data 0),
  .rz (1) 2 (.data 0),
  .rz (1) 3 (.data 2),
  .cz (.data 2) (.data 1),
  .rz (1) 2 (.data 1),
  .sx (.data 1),
  .rz (1) 2 (.data 1),
  .cz (.data 2) (.data 0),
  .rz (1) 2 (.data 0),
  .sx (.data 0),
  .rz (1) 2 (.data 0),
  .rz (1) 2 (.data 2),
  .sx (.data 2),
  .rz (1) 2 (.data 2),
  .rz (1) 2 (.data 2),
  .rz (1) 1 (.data 2),
  .rz (1) 2 (.data 2),
  .sx (.data 2),
  .rz (1) 2 (.data 2),
  .measure (.data 2) 0,
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.sx (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.cz (.data 2) (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.sx (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 2)),
  .ifBit 0 (.sx (.data 2)),
  .ifBit 0 (.rz (1) 2 (.data 2)),
  .ifBit 0 (.cz (.data 1) (.data 2)),
  .ifBit 0 (.rz (1) 2 (.data 2)),
  .ifBit 0 (.sx (.data 2)),
  .ifBit 0 (.rz (1) 2 (.data 2)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.sx (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.cz (.data 2) (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.sx (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.cz (.data 2) (.data 0)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.sx (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.cz (.data 2) (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.sx (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 2)),
  .ifBit 0 (.sx (.data 2)),
  .ifBit 0 (.rz (1) 2 (.data 2)),
  .ifBit 0 (.cz (.data 1) (.data 2)),
  .ifBit 0 (.rz (1) 2 (.data 2)),
  .ifBit 0 (.sx (.data 2)),
  .ifBit 0 (.rz (1) 2 (.data 2)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.sx (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.cz (.data 2) (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.sx (.data 1)),
  .ifBit 0 (.rz (1) 2 (.data 1)),
  .ifBit 0 (.x (.data 2))
]

#guard gadgetPhys.length == 102

-- the reconstruction equals the tool's physical circuit, gate for gate
#guard (gadgetWitness?.bind fun w => (applyWitness .cz mbuCircuit w 3).toOption) == some gadgetPhys

-- the checks refuse a tampered witness: the first swap of a block moved to another edge leaves the
-- block's layout unrestored
def tamper (w : Witness) : Witness :=
  { w with blocks := w.blocks.map fun (i, body) =>
      (i, match body with | .swap 2 1 :: rest => .swap 2 0 :: rest | b => b) }

#guard (gadgetWitness?.bind fun w => (applyWitness .cz mbuCircuit (tamper w) 3).toOption) == none
-- the final layout is checked
#guard (gadgetWitness?.bind fun w => (applyWitness .cz mbuCircuit { w with final := [0, 1, 2] } 3).toOption) == none
-- the physical circuit is well formed (decided here; `Circuit.wf` is Physlib-side)
#guard (physCircuit 3 gadgetPhys).wf

end CQRV.Tests.HardwareWitness
