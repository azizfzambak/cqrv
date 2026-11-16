module

public import CQRV.Hardware.Check
public import CQRV.Hardware.Bound

/-!
# CQRV.Hardware.PhysGrade

Report §3.1, §5.3, §9.1.1; PHASE2_SPEC §C.3 (Stage 26c2, P1) — the **physical grade** of a physical
circuit on a target, Physlib-free, in the cqr closure, computed by the kernel in the physical
certificate:

* the physical qubits used, the two-qubit count, the mid-circuit measurements, the feed-forward
  count (one per conditioned basis gate, as `GradeExt` counts it);
* the **wall-clock depth** (ns, exact) under the ASAP model: a gate starts when all its qubits are
  free; a gate conditioned on a bit also waits for the end of the measurement that wrote the bit,
  plus the feed-forward latency `L` — a named parameter the fakes do not give, stated as an
  assumption by every certificate; the durations are the exact rationals of the target file's
  decimals (`HardwareTarget.durations`; a two-qubit gate's by its directed pair or the reverse; a
  missing duration is an error);
* the **physical bound**, a port of 25a's `physical_bound` (exact): δ plus each physical
  operation's calibrated rate on its qubit or edge (`RateTable`), plus the `n` data readouts at their final
  positions; mid-circuit measurements take the readout rate of their qubit (the labelled assumption);
  vacuous at `≥ 1`. Equal to the Python figure on all twelve artifacts (`hw/physgrade.py`,
  `tests/diff/hw_physgrade_check.py`).

Nothing here is a statement about noise beyond the bound's arithmetic, and nothing is "verified on
hardware".
-/

@[expose] public section

namespace CQRV.Hardware

open CQRV Lean

/-- PHASE2_SPEC §C.3 — the physical grade. -/
structure PhysGrade where
  qubits : Nat
  twoQubit : Nat
  midMeas : Nat
  feedForward : Nat
  /-- The wall-clock depth in ns (exact). -/
  depth : Rat
  /-- δ + Σ rates + data readouts (exact). -/
  bound : Rat
  /-- `1 ≤ bound`. -/
  vacuous : Bool
  deriving Repr, DecidableEq

/-! ## Durations and rates -/

/-- The duration of a basis gate (ns) on the device qubits `dev` (compact → device). -/
def durationOf (d : Durations) (b : TargetBasis) (dev : List Nat) : BasisGate → Except String Rat
  | .ifBit _ g => durationOf d b dev g
  | .measure (.data q) _ =>
    match d.measure.lookup (toString (dev.getD q 0)) with
    | some t => pure t
    | none => throw s!"durations: no measurement duration for qubit {dev.getD q 0}"
  | .cz (.data p) (.data q) => two "cz" p q
  | .cx (.data p) (.data q) => two "cx" p q
  | .rz _ _ (.data q) => one "rz" q
  | .sx (.data q) => one "sx" q
  | .x (.data q) => one "x" q
  | g => throw s!"durations: an operand of {repr g} is not a data qubit"
where
  one (op : String) (q : Nat) : Except String Rat :=
    match (d.gates.lookup op).bind fun tab => tab.lookup (toString (dev.getD q 0)) with
    | some t => pure t
    | none => throw s!"durations: no duration for {op} on qubit {dev.getD q 0}"
  two (op : String) (p q : Nat) : Except String Rat :=
    let a := dev.getD p 0
    let c := dev.getD q 0
    match d.gates.lookup op with
    | none => throw s!"durations: no table for {op}"
    | some tab =>
      match tab.lookup s!"{a},{c}" with
      | some t => pure t
      | none =>
        match tab.lookup s!"{c},{a}" with
        | some t => pure t
        | none => throw s!"durations: no duration for {op} on the edge {a},{c}"

/-- The calibrated rates as exact tables: `one_qubit_gate_error` per gate name and qubit,
`two_qubit_gate_error` per gate name and directed pair, `readout_error` per qubit (the decimal
strings of the calibration, read exactly). The certificate carries the tables restricted to its
used qubits as Lean literals. -/
structure RateTable where
  one : List (String × List (String × Rat))
  two : List (String × List (String × Rat))
  readout : List (String × Rat)
  deriving Repr

/-- A table `{key: "decimal", …}`, exactly. -/
def decimalTable (ctx : String) (j : Json) : Except String (List (String × Rat)) := do
  let o ← j.getObj?.mapError fun _ => s!"{ctx}: not an object"
  o.toList.mapM fun (k, v) => do
    let s ← v.getStr?.mapError fun _ => s!"{ctx}.{k}: not a string"
    match parseDecimalSci s with
    | some q => pure (k, q)
    | none => throw s!"{ctx}.{k}: `{s}` is not a decimal"

/-- The tables of a target's calibration. -/
def RateTable.ofCalibration (cal : Json) : Except String RateTable := do
  let tables (k : String) : Except String (List (String × List (String × Rat))) := do
    let o ← (← (cal.getObjVal? k).mapError fun _ => s!"calibration: missing {k}").getObj?.mapError
      fun _ => s!"calibration.{k}: not an object"
    o.toList.mapM fun (op, tab) => return (op, ← decimalTable s!"calibration.{k}.{op}" tab)
  return { one := ← tables "one_qubit_gate_error", two := ← tables "two_qubit_gate_error",
           readout := ← decimalTable "calibration.readout_error"
             (← (cal.getObjVal? "readout_error").mapError fun _ => "calibration: missing readout_error") }

/-- Keep the entries on the device qubits `dev` (keys `"q"` with `q ∈ dev`, or `"p,q"` with both in
`dev`). -/
def restrictKeys (dev : List Nat) (tab : List (String × Rat)) : List (String × Rat) :=
  tab.filter fun (k, _) => (k.splitOn ",").all fun s => match s.toNat? with
    | some q => dev.contains q
    | none => false

def RateTable.restrict (r : RateTable) (dev : List Nat) : RateTable :=
  { one := r.one.map fun (op, tab) => (op, restrictKeys dev tab),
    two := r.two.map fun (op, tab) => (op, restrictKeys dev tab),
    readout := restrictKeys dev r.readout }

def Durations.restrict (d : Durations) (dev : List Nat) : Durations :=
  { gates := d.gates.map fun (op, tab) => (op, restrictKeys dev tab), measure := restrictKeys dev d.measure }

/-- The calibrated error rate of a basis gate (one-qubit gates and measurements by qubit, two-qubit
gates by directed pair or the reverse), as 25a's `physical_bound`. -/
def rateOf (r : RateTable) (dev : List Nat) : BasisGate → Except String Rat
  | .ifBit _ g => rateOf r dev g
  | .measure (.data q) _ => readout q
  | .cz (.data p) (.data q) => two "cz" p q
  | .cx (.data p) (.data q) => two "cx" p q
  | .rz _ _ (.data q) => one "rz" q
  | .sx (.data q) => one "sx" q
  | .x (.data q) => one "x" q
  | g => throw s!"calibration: an operand of {repr g} is not a data qubit"
where
  readout (q : Nat) : Except String Rat :=
    match r.readout.lookup (toString (dev.getD q 0)) with
    | some x => pure x
    | none => throw s!"calibration: no readout error for qubit {dev.getD q 0}"
  one (op : String) (q : Nat) : Except String Rat :=
    match (r.one.lookup op).bind fun tab => tab.lookup (toString (dev.getD q 0)) with
    | some x => pure x
    | none => throw s!"calibration: no {op} error for qubit {dev.getD q 0}"
  two (op : String) (p q : Nat) : Except String Rat :=
    let a := dev.getD p 0
    let c := dev.getD q 0
    match r.two.lookup op with
    | none => throw s!"calibration: no table for {op}"
    | some tab =>
      match tab.lookup s!"{a},{c}" with
      | some x => pure x
      | none =>
        match tab.lookup s!"{c},{a}" with
        | some x => pure x
        | none => throw s!"calibration: no {op} error for the edge {a},{c}"

/-! ## Counts -/

def BasisGate.isTwoQubit : BasisGate → Bool
  | .cz _ _ | .cx _ _ => true
  | .ifBit _ g => g.isTwoQubit
  | _ => false

def BasisGate.isMeasure : BasisGate → Bool
  | .measure _ _ => true
  | .ifBit _ g => g.isMeasure
  | _ => false

def BasisGate.isConditioned : BasisGate → Bool
  | .ifBit _ _ => true
  | _ => false

/-! ## The ASAP schedule -/

/-- The clock of the schedule: the time each compact qubit is free, and the end time of the
measurement that wrote each classical bit. -/
structure Clock where
  qubits : List Rat
  bits : List (Nat × Rat)

def Clock.init (N : Nat) : Clock := ⟨List.replicate N 0, []⟩

def Clock.qubitTime (c : Clock) (q : Nat) : Rat := c.qubits.getD q 0

def Clock.bitTime (c : Clock) (j : Nat) : Rat := (c.bits.lookup j).getD 0

/-- One gate under the ASAP model with feed-forward latency `L`: it starts when its qubits are free
(and, conditioned, after the measurement of its bit plus `L`), lasts its duration, and a
measurement records the end time of its bit. -/
def Clock.step (L : Rat) (c : Clock) (g : BasisGate) (dur : Rat) : Clock :=
  let inner := g.stripIf
  let qs := inner.qubits.filterMap fun q => match q with | .data i => some i | .anc _ => none
  let startQ := qs.foldl (fun m q => max m (c.qubitTime q)) 0
  let start := match g with
    | .ifBit j _ => max startQ (c.bitTime j + L)
    | _ => startQ
  let fin := start + dur
  let qubits := qs.foldl (fun l q => modifyAt (fun _ => fin) q l) c.qubits
  let bits := match inner with
    | .measure _ j => (j, fin) :: c.bits
    | _ => c.bits
  ⟨qubits, bits⟩

/-- The wall-clock depth of a schedule: the latest time anything is busy. -/
def Clock.depth (c : Clock) : Rat :=
  max (c.qubits.foldl max 0) (c.bits.foldl (fun m p => max m p.2) 0)

/-! ## The grade -/

/-- PHASE2_SPEC §C.3 (Stage 26c2, P1) — **`physGrade`**: the physical grade of the physical circuit
`G` (compact register of `dev.length` qubits, `dev` the device qubits) on the target `t` with basis
`b`, feed-forward latency `L` (ns), the data readouts at the device qubits `dataPhys` (the final
layout's data positions), and the logical δ. An error names the missing duration or rate. -/
def physGrade (d : Durations) (r : RateTable) (b : TargetBasis) (dev : List Nat) (G : List BasisGate)
    (L : Rat) (dataPhys : List Nat) (delta : Rat) : Except String PhysGrade := do
  let clock ← G.foldlM (fun (c : Clock) g => do
      let t ← durationOf d b dev g
      return c.step L g t) (Clock.init dev.length)
  let rates ← G.mapM (rateOf r dev)
  let readouts ← dataPhys.mapM fun p => match r.readout.lookup (toString p) with
    | some x => pure x
    | none => throw s!"calibration: no readout error for the data qubit {p}"
  let total := rates.foldl (· + ·) 0 + readouts.foldl (· + ·) 0
  let bound := delta + total
  return { qubits := dev.length,
           twoQubit := (G.filter BasisGate.isTwoQubit).length,
           midMeas := (G.filter BasisGate.isMeasure).length,
           feedForward := (G.filter BasisGate.isConditioned).length,
           depth := clock.depth,
           bound,
           vacuous := decide (1 ≤ bound) }

/-- The grade from a target (the tables of its calibration). -/
def physGradeOf (t : HardwareTarget) (b : TargetBasis) (dev : List Nat) (G : List BasisGate) (L : Rat)
    (dataPhys : List Nat) (delta : Rat) : Except String PhysGrade := do
  physGrade t.durations (← RateTable.ofCalibration t.calibration) b dev G L dataPhys delta

/-- The grade as canonical JSON (exact fractions as strings; the form `hw/physgrade.py` prints). -/
def PhysGrade.toJson (g : PhysGrade) (L : Rat) : Json :=
  Json.mkObj [("qubits", g.qubits), ("two_qubit", g.twoQubit), ("mid_measurements", g.midMeas),
    ("feed_forward", g.feedForward), ("depth_ns", ratStr g.depth), ("bound", ratStr g.bound),
    ("vacuous", g.vacuous), ("ff_latency_ns", ratStr L)]

end CQRV.Hardware
