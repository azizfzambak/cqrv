module

import CQRV.Hardware.Bound
import CQRV.Circuit.Restoration
meta import CQRV.Hardware.Bound
meta import CQRV.Circuit.Restoration

/-!
# Tests for `CQRV.Hardware.Bound` (Stage 24c; PHASE2_SPEC §C.1 "Per-operation rates"; report
§3.1.3, §3.3.3)

`basisCounts` on the MBU gadget for both bases (counted by hand from the table), the mid-circuit /
final classification of a measurement, the exact decimal reader with exponents, the worst and
median aggregates, and `weightedBound` on a tiny two-qubit target.
-/

namespace CQRV.Tests.HardwareBound

open CQRV CQRV.Hardware

/-! ## The table on the MBU gadget

`mbuCircuit` = `TempLogicalAND` (h, t, cnot, cnot, cnot, cnot, tdg, tdg, t, cnot, cnot, h, s),
`z`, then `h`, `measure`, `if: cz`, `if: x`. By hand: 3 `h` ↦ 6 rz + 3 sx; 2 `t` + 2 `tdg` + `s` +
`z` ↦ 6 rz; 6 `cnot`; 1 `cz`; 1 `x`; the measurement is followed by gates, so mid-circuit. -/

#guard basisCounts .cz mbuCircuit ==
  { rz := 6 + 6 + 6 * 4, sx := 3 + 6 * 2, x := 1, twoQubit := 7, midMeas := 1, finalMeas := 0 }
#guard basisCounts .cx mbuCircuit ==
  { rz := 6 + 6 + 4, sx := 3 + 2, x := 1, twoQubit := 7, midMeas := 1, finalMeas := 0 }
#guard (basisCounts .cz mbuCircuit).total == 36 + 15 + 1 + 7 + 1

-- a measurement followed only by bookkeeping is final; followed by a gate, mid-circuit
#guard basisCounts .cz ⟨1, [.h (.data 0), .measure (.data 0) 0, .free (.anc 0)]⟩ ==
  { rz := 2, sx := 1, finalMeas := 1 }
#guard basisCounts .cz ⟨1, [.measure (.data 0) 0, .ifBit 0 (.x (.data 0))]⟩ ==
  { x := 1, midMeas := 1 }
-- `cp` through its five-gate decomposition: 3 rz and two controlled-NOTs
#guard basisCounts .cx ⟨2, [.cp 1 2 (.data 0) (.data 1)]⟩ == { rz := 3, twoQubit := 2 }
#guard basisCounts .cz ⟨2, [.cp 1 2 (.data 0) (.data 1)]⟩ == { rz := 3 + 8, sx := 4, twoQubit := 2 }

#guard TargetBasis.ofGates ["cz", "id", "rz", "sx", "x"] == .ok .cz
#guard TargetBasis.ofGates ["cx", "id", "rz", "sx", "x"] == .ok .cx
#guard (TargetBasis.ofGates ["rz", "sx"]).toOption.isNone
#guard (TargetBasis.ofGates ["cz", "cx"]).toOption.isNone

/-! ## The decimal reader and the aggregates -/

#guard parseDecimalSci "8e-05" == some (8 / 100000 : Rat)
#guard parseDecimalSci "0.0001" == some (1 / 10000 : Rat)
#guard parseDecimalSci "1.2E+3" == some (1200 : Rat)
#guard parseDecimalSci "0.004854875406855308" == some (4854875406855308 / 10 ^ 18 : Rat)
#guard parseDecimalSci "1" == some (1 : Rat)
#guard (parseDecimalSci "abc").isNone
#guard (parseDecimalSci "1e").isNone
#guard (parseDecimalSci "-0.1").isNone

#guard worstOf [(3 : Rat), 1, 2] == some 3
#guard medianOf [(3 : Rat), 1, 2] == some 2
#guard medianOf [(1 : Rat), 2, 3, 4] == some (5 / 2)
#guard (medianOf ([] : List Rat)).isNone

/-! ## `weightedBound` on a tiny target -/

def tinyText : String := r#"{
  "schema_version": "1.0.0", "name": "tiny", "num_qubits": 2,
  "basis_gates": ["cz", "rz", "sx", "x"], "coupling_map": [[0, 1], [1, 0]],
  "capabilities": {"mid_circuit_measurement": {"value": true, "source": "hand"},
                   "feed_forward": {"value": true, "source": "hand"}, "reset": {"value": true, "source": "hand"}},
  "calibration": {"source": "hand-written test values",
                  "one_qubit_gate_error": {"rz": {"0": "0.0", "1": "0.0"}, "sx": {"0": "0.001", "1": "0.003"},
                                           "x": {"0": "0.002", "1": "0.002"}},
                  "two_qubit_gate_error": {"cz": {"0,1": "0.01"}},
                  "readout_error": {"0": "0.02", "1": "0.04"},
                  "mid_circuit_measurement_error": null, "mid_circuit_measurement_note": "none",
                  "t1_s": {}, "t2_s": {}},
  "snapshot": {"timestamp": "2026-11-15", "hash": "0000000000000000000000000000000000000000000000000000000000000000"}
}"#

def tiny? : Option HardwareTarget := (HardwareTarget.parse tinyText).toOption
def rates? : Option Rates := tiny?.bind fun t => (Rates.ofTarget t .cz).toOption

#guard tiny?.isSome
#guard rates?.isSome
#guard rates?.map (·.sx.worst) == some (3 / 1000)
#guard rates?.map (·.sx.median) == some (2 / 1000)
#guard rates?.map (·.readout.median) == some (3 / 100)
#guard rates?.map (·.twoQubit.entries) == some 1

/-- The MBU gadget on the tiny target with δ = 0 and the two data qubits read out:
worst = 15 · 0.003 + 1 · 0.002 + 7 · 0.01 + 3 · 0.04 = 0.237; median = 15 · 0.002 + 0.002 + 0.07 +
3 · 0.03 = 0.192. -/
def report? : Option BoundReport := rates?.map fun r => BoundReport.mk' .cz mbuCircuit 2 r 0

#guard report?.map (·.worst) == some (237 / 1000)
#guard report?.map (·.median) == some (192 / 1000)
#guard report?.map (·.vacuous) == some false
#guard report?.map (·.etaMidCoeff) == some 1
#guard (report?.map fun R => ratStr R.worst) == some "237/1000"
#guard ratStr (3 : Rat) == "3"

-- with δ = 4/5 the worst case passes 1: vacuous
#guard (rates?.map fun r => (BoundReport.mk' .cz mbuCircuit 2 r (4 / 5)).vacuous) == some true

end CQRV.Tests.HardwareBound
