module

import CQRV.Hardware.Target
meta import CQRV.Hardware.Target

/-!
# Tests for `CQRV.Hardware.Target` (Stage 24a; PHASE2_SPEC §C.1; report §3.1.3, §5.3)

`HardwareTarget.ofJson` on a small inline two-qubit target (pretty-printed, keys out of order,
so that the canonical form is exercised), its fields, the canonical `calibration` (byte-identical
to Python's `json.dumps(sort_keys=True, separators=(",", ":"))`), `checkHash` against the digest
of `hashlib.sha3_256` on that string (the test oracle), a corrupted calibration number failing
the check, the uncomputation modes with and without feed forward, and the errors of a malformed
target.
-/

namespace CQRV.Tests.HardwareTarget

open CQRV.Hardware

/-- A two-qubit target, hand-written (not measured); the hash is `hashlib.sha3_256` of the
canonical `calibration` below. -/
def miniText : String := r#"{
  "snapshot": {"timestamp": "2026-11-15T00:00:00Z",
               "hash": "8005fd6f46dc124fa9140e14a55983709c4a1c8d335fc8734c6302968c9a39da"},
  "schema_version": "1.0.0",
  "name": "mini_two_qubit",
  "source": {"class": "hand-written", "note": "test target, not a backend"},
  "num_qubits": 2,
  "basis_gates": ["cz", "rz", "sx", "x"],
  "coupling_map": [[0, 1], [1, 0]],
  "capabilities": {
    "reset": {"value": true, "source": "hand-written"},
    "feed_forward": {"value": true, "source": "hand-written"},
    "mid_circuit_measurement": {"value": true, "source": "hand-written"}
  },
  "durations": {"source": "hand-written", "unit": "ns",
                "gates": {"sx": {"0": 35.55555555555556, "1": 35.55555555555556},
                          "cz": {"0,1": 68.0}},
                "measure": {"0": 1560.0, "1": 1560.0}},
  "calibration": {
    "two_qubit_gate_error": {"cz": {"0,1": "0.005"}},
    "t2_s": {"1": "9e-05", "0": "8e-05"},
    "t1_s": {"0": "0.0001", "1": "0.00012"},
    "source": "hand-written test values, not measured",
    "readout_error": {"0": "0.01", "1": "0.02"},
    "one_qubit_gate_error": {"x": {"0": "0.0002", "1": "0.0003"},
                             "sx": {"1": "0.0003", "0": "0.0002"}},
    "mid_circuit_measurement_note": "no source",
    "mid_circuit_measurement_error": null
  }
}"#

/-- Python's canonical form of the `calibration` above. -/
def miniCanonical : String :=
  "{\"mid_circuit_measurement_error\":null,\"mid_circuit_measurement_note\":\"no source\"," ++
  "\"one_qubit_gate_error\":{\"sx\":{\"0\":\"0.0002\",\"1\":\"0.0003\"},\"x\":{\"0\":\"0.0002\"," ++
  "\"1\":\"0.0003\"}},\"readout_error\":{\"0\":\"0.01\",\"1\":\"0.02\"},\"source\":\"hand-written " ++
  "test values, not measured\",\"t1_s\":{\"0\":\"0.0001\",\"1\":\"0.00012\"},\"t2_s\":{\"0\":" ++
  "\"8e-05\",\"1\":\"9e-05\"},\"two_qubit_gate_error\":{\"cz\":{\"0,1\":\"0.005\"}}}"

def mini? : Option HardwareTarget := (HardwareTarget.parse miniText).toOption

#guard mini?.isSome
#guard mini?.map (·.name) == some "mini_two_qubit"
#guard mini?.map (·.numQubits) == some 2
#guard mini?.map (·.basisGates) == some ["cz", "rz", "sx", "x"]
#guard mini?.map (·.couplingMap) == some [(0, 1), (1, 0)]
#guard mini?.map (·.capabilities.feedForward) == some ⟨true, "hand-written"⟩
#guard mini?.map (·.snapshotTimestamp) == some "2026-11-15T00:00:00Z"

/-! ## The canonical form and the hash -/

#guard mini?.map (fun t => canonical t.calibration) == some miniCanonical
#guard mini?.map (·.calibrationHash) ==
  some "8005fd6f46dc124fa9140e14a55983709c4a1c8d335fc8734c6302968c9a39da"
#guard mini?.map (·.checkHash) == some true
#guard mini?.map (·.uncomputeModes) == some ["mbu", "coherent"]

/-- One calibration digit changed: the canonical form changes and the hash check fails
(`hashlib` gives e358c775… for the changed string). -/
def corrupt? : Option HardwareTarget :=
  (HardwareTarget.parse (miniText.replace "\"0.005\"" "\"0.006\"")).toOption

#guard corrupt?.map (·.checkHash) == some false
#guard corrupt?.map (·.calibrationHash) ==
  some "e358c7755b6520d3f5fa83b73e10841fd7edb90ba69aebea8bce976c72f5048a"

/-- Feed forward off: `coherent` only. -/
def noFF? : Option HardwareTarget :=
  (HardwareTarget.parse (miniText.replace "\"feed_forward\": {\"value\": true"
    "\"feed_forward\": {\"value\": false")).toOption

#guard noFF?.map (·.uncomputeModes) == some ["coherent"]
#guard noFF?.map (·.checkHash) == some true

/-! ## Malformed targets -/

-- a wrong schema version
#guard (HardwareTarget.parse (miniText.replace "\"1.0.0\"" "\"0.9.0\"")).toOption.isNone

-- an edge outside `num_qubits`
#guard (HardwareTarget.parse (miniText.replace "[1, 0]" "[1, 2]")).toOption.isNone

-- an empty capability source
#guard (HardwareTarget.parse (miniText.replace "\"reset\": {\"value\": true, \"source\": \"hand-written\"}"
  "\"reset\": {\"value\": true, \"source\": \"\"}")).toOption.isNone

-- not JSON at all
#guard (HardwareTarget.parse "not json").toOption.isNone

end CQRV.Tests.HardwareTarget
