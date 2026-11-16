module

public import Lean.Data.Json
public import CQRV.Certify.SHA3
public import Mathlib.Data.Rat.Defs

/-!
# CQRV.Hardware.Target

Report §3.1.3 (hardware profiles as a change of base), §5.3 (the emitter and the trust
boundary); PHASE2_SPEC §C.1 (Stage 24a, Track C) — reading a `HardwareTarget` JSON file
(`docs/hardware_target.schema.json` v1.0.0, written by the untrusted `hw/target.py` from a
Qiskit fake backend) for `cqr hw capabilities`. Physlib-free: Lean core JSON and the SHA3-256 of
`CQRV.Certify.SHA3`.

Lean reads the fields it needs — `name`, `num_qubits`, `basis_gates`, `coupling_map`, the three
capability flags with their sources, `calibration` and `snapshot` — and checks the snapshot hash:
the SHA3-256 of the canonical form of `calibration` must equal `snapshot.hash`.

**The canonical form** (DECISIONS.md 2026-11-15, Stage 24a) is `Lean.Json.compress` of the parsed
object: keys sorted by code point, no whitespace, strings escaped as `\"`, `\\`, `\n`, `\r` and
`\u00XX` below 0x20, everything else as UTF-8. Python writes the whole file in this form
(`json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)` and a trailing
newline), and every number inside `calibration` is a decimal **string** (Python's `repr` of the
float the source gives), so that no number is re-printed on either side and the two canonical
forms are byte-identical. Numbers outside `calibration` (`num_qubits`, the coupling map, the
durations) are JSON numbers; they are not hashed.
-/

@[expose] public section

namespace CQRV.Hardware

open Lean

/-- The schema version of target files (`docs/hardware_target.schema.json`). -/
def targetSchemaVersion : String := "1.0.0"

/-- PHASE2_SPEC §C.1 — a capability flag and where it was read from. -/
structure Capability where
  value : Bool
  source : String
  deriving Repr, BEq

/-- PHASE2_SPEC §C.1 — the three capabilities: mid-circuit measurement, feed forward
(classically conditioned operations, Qiskit's `if_else`), reset. -/
structure Capabilities where
  midCircuitMeasurement : Capability
  feedForward : Capability
  reset : Capability
  deriving Repr, BEq

/-- PHASE2_SPEC §C.3 (Stage 26c2) — the `durations` of a target, in ns, as the exact rationals of the
decimal numbers written in the file (`JsonNumber`, exact): per gate name, per qubit (`"q"`) or per
directed pair (`"p,q"`); the measurement durations per qubit. Not covered by the snapshot hash. -/
structure Durations where
  gates : List (String × List (String × Rat))
  measure : List (String × Rat)
  deriving Repr

/-- A JSON number, exactly: `mantissa / 10^exponent`. -/
def jsonNumberToRat (n : JsonNumber) : Rat := (n.mantissa : Rat) / ((10 ^ n.exponent : Nat) : Rat)

/-- PHASE2_SPEC §C.1 — the fields of a hardware target that Lean reads. -/
structure HardwareTarget where
  name : String
  numQubits : Nat
  basisGates : List String
  /-- The directed edges of the coupling map. -/
  couplingMap : List (Nat × Nat)
  capabilities : Capabilities
  /-- The `calibration` object as parsed; it is hashed in its canonical form. -/
  calibration : Json
  snapshotTimestamp : String
  /-- `snapshot.hash`: the SHA3-256 hex digest the file claims for `calibration`. -/
  snapshotHash : String
  /-- The gate and measurement durations (Stage 26c2). -/
  durations : Durations

/-- A key of an object, with a message naming the context. -/
def field (ctx : String) (j : Json) (k : String) : Except String Json :=
  (j.getObjVal? k).mapError fun _ => s!"{ctx}: missing key `{k}`"

/-- A string-valued key. -/
def strField (ctx : String) (j : Json) (k : String) : Except String String := do
  (← field ctx j k).getStr?.mapError fun _ => s!"{ctx}: `{k}` must be a string"

/-- A natural-number-valued key. -/
def natField (ctx : String) (j : Json) (k : String) : Except String Nat := do
  (← field ctx j k).getNat?.mapError fun _ => s!"{ctx}: `{k}` must be a natural number"

/-- An array-valued key. -/
def arrField (ctx : String) (j : Json) (k : String) : Except String (Array Json) := do
  (← field ctx j k).getArr?.mapError fun _ => s!"{ctx}: `{k}` must be an array"

/-- A capability flag `{value, source}`; the source must be non-empty, so that no flag enters
without saying where it was read from. -/
def Capability.ofJson (ctx : String) (j : Json) : Except String Capability := do
  let v ← (← field ctx j "value").getBool?.mapError fun _ => s!"{ctx}: `value` must be a boolean"
  let s ← strField ctx j "source"
  if s.isEmpty then throw s!"{ctx}: empty `source`"
  return ⟨v, s⟩

/-- A directed edge `[i, j]` of the coupling map, both endpoints below `n`. -/
def edgeOfJson (n : Nat) (j : Json) : Except String (Nat × Nat) := do
  let a ← j.getArr?.mapError fun _ => "coupling_map: an edge must be an array"
  match a.toList with
  | [x, y] =>
    let x ← x.getNat?.mapError fun _ => "coupling_map: a qubit index must be a natural number"
    let y ← y.getNat?.mapError fun _ => "coupling_map: a qubit index must be a natural number"
    unless x < n ∧ y < n do throw s!"coupling_map: edge [{x}, {y}] outside num_qubits = {n}"
    return (x, y)
  | _ => throw "coupling_map: an edge must have two endpoints"

/-- A table `{key: number, …}` read exactly. -/
def numberTable (ctx : String) (j : Json) : Except String (List (String × Rat)) := do
  let o ← j.getObj?.mapError fun _ => s!"{ctx}: not an object"
  o.toList.mapM fun (k, v) => do
    let n ← v.getNum?.mapError fun _ => s!"{ctx}.{k}: not a number"
    return (k, jsonNumberToRat n)

/-- PHASE2_SPEC §C.3 (Stage 26c2) — `durations` from its JSON object; the unit must be `ns`. -/
def Durations.ofJson (j : Json) : Except String Durations := do
  let unit ← strField "durations" j "unit"
  unless unit == "ns" do throw s!"durations: unit {unit}, expected ns"
  let gatesObj ← (← field "durations" j "gates").getObj?.mapError fun _ => "durations.gates: not an object"
  let gates ← gatesObj.toList.mapM fun (op, tab) => do
    return (op, ← numberTable s!"durations.gates.{op}" tab)
  let measure ← numberTable "durations.measure" (← field "durations" j "measure")
  return { gates, measure }

/-- PHASE2_SPEC §C.1 — a target from its JSON object (the fields Lean needs; the other fields of
the schema are left to the Python check). -/
def HardwareTarget.ofJson (j : Json) : Except String HardwareTarget := do
  let v ← strField "target" j "schema_version"
  unless v == targetSchemaVersion do
    throw s!"target: schema_version {v}, expected {targetSchemaVersion}"
  let name ← strField "target" j "name"
  if name.isEmpty then throw "target: empty `name`"
  let numQubits ← natField "target" j "num_qubits"
  let basisGates ← (← arrField "target" j "basis_gates").toList.mapM fun g =>
    g.getStr?.mapError fun _ => "basis_gates: a gate name must be a string"
  let couplingMap ← (← arrField "target" j "coupling_map").toList.mapM (edgeOfJson numQubits)
  let caps ← field "target" j "capabilities"
  let cap (k : String) : Except String Capability := do
    Capability.ofJson s!"capabilities.{k}" (← field "capabilities" caps k)
  let capabilities : Capabilities :=
    ⟨← cap "mid_circuit_measurement", ← cap "feed_forward", ← cap "reset"⟩
  let calibration ← field "target" j "calibration"
  let _ ← calibration.getObj?.mapError fun _ => "target: `calibration` must be an object"
  let snap ← field "target" j "snapshot"
  let snapshotTimestamp ← strField "snapshot" snap "timestamp"
  let snapshotHash ← strField "snapshot" snap "hash"
  -- `durations` (Stage 26c2): read when present; a target without it has none (a lookup then fails)
  let durations ← match j.getObjVal? "durations" with
    | .ok dj => Durations.ofJson dj
    | .error _ => pure ⟨[], []⟩
  return { name, numQubits, basisGates, couplingMap, capabilities, calibration,
           snapshotTimestamp, snapshotHash, durations }

/-- The canonical form of a JSON value: `Lean.Json.compress` (sorted keys, no whitespace). -/
def canonical (j : Json) : String := j.compress

/-- Report §9.5.3 idiom — the SHA3-256 hex digest of the canonical `calibration`. -/
def HardwareTarget.calibrationHash (t : HardwareTarget) : String :=
  Certify.SHA3.sha3String (canonical t.calibration)

/-- PHASE2_SPEC §C.1 — the hash check: Lean's SHA3-256 of the canonical `calibration` equals
`snapshot.hash`. -/
def HardwareTarget.checkHash (t : HardwareTarget) : Bool :=
  t.calibrationHash == t.snapshotHash

/-- PHASE2_SPEC §C.1 — the uncomputation modes the target supports: `mbu` needs mid-circuit
measurement and feed forward; `coherent` needs neither. -/
def HardwareTarget.uncomputeModes (t : HardwareTarget) : List String :=
  if t.capabilities.midCircuitMeasurement.value && t.capabilities.feedForward.value then
    ["mbu", "coherent"]
  else ["coherent"]

/-- Parse a target file's text. -/
def HardwareTarget.parse (text : String) : Except String HardwareTarget := do
  HardwareTarget.ofJson (← Json.parse text)

/-- Read a target file; a missing or unreadable file, or a malformed target, is an error message
(the CLI exits 2 on it). -/
def readTarget (path : String) : IO (Except String HardwareTarget) := do
  try
    let text ← IO.FS.readFile path
    return (HardwareTarget.parse text).mapError (s!"{path}: " ++ ·)
  catch e => return .error s!"{path}: {e}"

end CQRV.Hardware
