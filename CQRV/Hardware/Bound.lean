module

public import CQRV.Hardware.Target
public import CQRV.Circuit.IR
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Basic

/-!
# CQRV.Hardware.Bound

Report §3.1.3 (hardware profiles as a change of base), §3.3.3 (δ_hw ≤ δ + G·p̄), §5.3;
PHASE2_SPEC §C.1 "Per-operation rates" and the 24b refinement (Stage 24c, Track C) — the
per-operation-type counts of an IR circuit under a fixed decomposition table per target basis,
the rates of each basis operation read exactly from a target's calibration snapshot, and the
weighted bound δ_hw ≤ δ + Σ_types count · rate. Physlib-free.

* **The table** (`gateCounts`; stated here, proved in Stage 26's `decomp_sound`): for the `cz`
  basis `h ↦ rz sx rz`, `x ↦ x`, `s sdg t tdg z p ↦ rz`, `cnot ↦ h(t) cz h(t)`, `cz ↦ cz`; for the
  `cx` basis `cnot ↦ cx`, `cz ↦ h(t) cx h(t)`, the rest the same; `cp` by its five-gate
  decomposition (`Circuit.decomposeCp`: three `p` and two `cnot`). A conditioned gate counts as
  executed (a union bound over all branches); `alloc` and `free` count nothing.
* **Measurements** (`basisCounts`): a `measure` is mid-circuit when a gate other than `alloc` /
  `free` follows it anywhere in the circuit; otherwise it is final.
* **Rates** (`Rates.ofTarget`): every calibration value is a decimal string; `parseDecimalSci`
  reads it exactly into ℚ. The **worst** rate of a basis operation is the maximum over the
  device's qubits or edges — sound for any layout; the **median** is "typical, not a bound". The
  snapshot gives no mid-circuit measurement error, so the mid-circuit term uses the readout rate
  as a labelled assumption (its coefficient `midMeas` is reported separately).
* **The bound** (`weightedBound`): δ + Σ count · rate, exact in ℚ; vacuous when ≥ 1. Nothing
  here is certified: `cqr hw bound` reports it (Stage 27 proves the premise).
-/

@[expose] public section

namespace CQRV.Hardware

open Lean

/-- PHASE2_SPEC §C.1 — the two-qubit basis of a target: `cz` (the Heron fakes) or `cx` (the
Eagle fakes), read from `basis_gates`. -/
inductive TargetBasis where
  | cz
  | cx
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The name of the two-qubit basis gate. -/
def TargetBasis.twoQubit : TargetBasis → String
  | .cz => "cz"
  | .cx => "cx"

/-- The basis of a target from its `basis_gates`; neither `cz` nor `cx` (or both) is an error. -/
def TargetBasis.ofGates (gates : List String) : Except String TargetBasis :=
  match gates.contains "cz", gates.contains "cx" with
  | true, false => pure .cz
  | false, true => pure .cx
  | true, true => throw "target basis has both cz and cx; the table needs one two-qubit basis gate"
  | false, false => throw s!"target basis {gates} has neither cz nor cx"

/-- The counts of a circuit under the table: the one-qubit basis gates by name (`rz`, `sx`, `x`;
`id` is never emitted), the two-qubit basis gate, the mid-circuit and the final measurements. -/
structure BasisCounts where
  rz : Nat := 0
  sx : Nat := 0
  x : Nat := 0
  twoQubit : Nat := 0
  midMeas : Nat := 0
  finalMeas : Nat := 0
  deriving Repr, DecidableEq, BEq, Inhabited

def BasisCounts.add (a b : BasisCounts) : BasisCounts :=
  ⟨a.rz + b.rz, a.sx + b.sx, a.x + b.x, a.twoQubit + b.twoQubit, a.midMeas + b.midMeas,
   a.finalMeas + b.finalMeas⟩

instance : Add BasisCounts := ⟨BasisCounts.add⟩

/-- `n` copies of a count. -/
def BasisCounts.smul (n : Nat) (c : BasisCounts) : BasisCounts :=
  ⟨n * c.rz, n * c.sx, n * c.x, n * c.twoQubit, n * c.midMeas, n * c.finalMeas⟩

/-- The table — `h ↦ rz sx rz`. -/
def hCounts : BasisCounts := { rz := 2, sx := 1 }

/-- The table — the controlled-NOT in each basis: `cx` itself, or `h(t) cz h(t)`. -/
def cnotCounts : TargetBasis → BasisCounts
  | .cx => { twoQubit := 1 }
  | .cz => hCounts + { twoQubit := 1 } + hCounts

/-- The table — the controlled-Z in each basis: `cz` itself, or `h(t) cx h(t)`. -/
def czCounts : TargetBasis → BasisCounts
  | .cz => { twoQubit := 1 }
  | .cx => hCounts + { twoQubit := 1 } + hCounts

/-- PHASE2_SPEC §C.1 (24b refinement) — the table for one gate (measurements are classified by
`basisCounts`, which knows what follows them). -/
def gateCounts (b : TargetBasis) : Gate → BasisCounts
  | .h _ => hCounts
  | .x _ => { x := 1 }
  | .s _ | .sdg _ | .t _ | .tdg _ | .z _ | .p _ _ _ => { rz := 1 }
  | .cnot _ _ => cnotCounts b
  | .cz _ _ => czCounts b
  | .cp _ _ _ _ => { rz := 3 } + BasisCounts.smul 2 (cnotCounts b)
  | .ifBit _ g => gateCounts b g
  | .measure _ _ | .alloc _ | .free _ => {}

/-- A gate that is not bookkeeping. -/
def Gate.isOp : Gate → Bool
  | .alloc _ | .free _ => false
  | _ => true

/-- PHASE2_SPEC §C.1 — the counts of a circuit: the table on every gate, and each `measure`
classified as mid-circuit (an operation follows it) or final. -/
def basisCounts (b : TargetBasis) (C : Circuit) : BasisCounts :=
  go C.gates
where
  go : List Gate → BasisCounts
    | [] => {}
    | .measure _ _ :: rest =>
      (if rest.any Gate.isOp then { midMeas := 1 } else { finalMeas := 1 }) + go rest
    | g :: rest => gateCounts b g + go rest

/-- The total number of basis operations counted (the `G` of the old p̄ form, under the table). -/
def BasisCounts.total (c : BasisCounts) : Nat :=
  c.rz + c.sx + c.x + c.twoQubit + c.midMeas + c.finalMeas

/-! ## The exact decimal reader -/

/-- Parse an unsigned decimal with an optional exponent exactly: `"0.01"`, `"2"`, `"1.5"`,
`"8e-05"`, `"1.2E+3"` (`[0-9]+(\.[0-9]+)?([eE][-+]?[0-9]+)?`), the form Python's `repr` prints
for a finite non-negative float. Generalizes `CQRV.parseDecimal` (Stage 11b, for p̄). -/
def parseDecimalSci (s : String) : Option Rat :=
  let digits (t : String) : Option Nat :=
    if t.isEmpty || !t.all Char.isDigit then none else t.toNat?
  let mantissa (m : String) : Option Rat :=
    match m.splitOn "." with
    | [i] => (digits i).map fun n => (n : Rat)
    | [i, f] => do
      let n ← digits i
      let k ← digits f
      return (n : Rat) + (k : Rat) / ((10 ^ f.length : Nat) : Rat)
    | _ => none
  let exponent (e : String) : Option Int :=
    if e.startsWith "-" then (digits (e.drop 1).toString).map fun n => -(n : Int)
    else if e.startsWith "+" then (digits (e.drop 1).toString).map fun n => (n : Int)
    else (digits e).map fun n => (n : Int)
  match (s.replace "E" "e").splitOn "e" with
  | [m] => mantissa m
  | [m, e] => do
    let q ← mantissa m
    let k ← exponent e
    return if k ≥ 0 then q * ((10 ^ k.toNat : Nat) : Rat)
      else q / ((10 ^ (-k).toNat : Nat) : Rat)
  | _ => none

/-! ## Rates -/

/-- The values of an object `{key: "decimal", …}` of the calibration, read exactly. -/
def decimalValues (ctx : String) (j : Json) : Except String (List Rat) := do
  let o ← j.getObj?.mapError fun _ => s!"{ctx}: not an object"
  o.toList.mapM fun (k, v) => do
    let s ← v.getStr?.mapError fun _ => s!"{ctx}.{k}: not a string"
    match parseDecimalSci s with
    | some q => pure q
    | none => throw s!"{ctx}.{k}: `{s}` is not a decimal"

/-- The maximum of a non-empty list — the worst case over the device. -/
def worstOf (l : List Rat) : Option Rat := l.max?

/-- The median of a non-empty list (the mean of the two middle values when the length is even) —
"typical, not a bound". -/
def medianOf (l : List Rat) : Option Rat :=
  let s := l.mergeSort (fun a b => decide (a ≤ b))
  let n := s.length
  if n = 0 then none
  else if n % 2 = 1 then s[n / 2]?
  else do
    let a ← s[n / 2 - 1]?
    let b ← s[n / 2]?
    return (a + b) / 2

/-- Both aggregates of one basis operation, with the number of entries. -/
structure Rate where
  worst : Rat
  median : Rat
  entries : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

def Rate.ofList (ctx : String) (l : List Rat) : Except String Rate := do
  match worstOf l, medianOf l with
  | some w, some m => pure ⟨w, m, l.length⟩
  | _, _ => throw s!"{ctx}: no entries in the snapshot"

/-- The rates of the basis operations the table uses, from a target's `calibration`: `rz`, `sx`,
`x` from `one_qubit_gate_error`, the two-qubit gate from `two_qubit_gate_error`, readout from
`readout_error`. The mid-circuit measurement error is absent from the snapshot (null); the
mid-circuit term uses `readout` as a labelled assumption. -/
structure Rates where
  rz : Rate
  sx : Rate
  x : Rate
  twoQubit : Rate
  readout : Rate
  deriving Repr, DecidableEq, BEq, Inhabited

def Rates.ofTarget (t : HardwareTarget) (b : TargetBasis) : Except String Rates := do
  let cal := t.calibration
  let one ← field "calibration" cal "one_qubit_gate_error"
  let two ← field "calibration" cal "two_qubit_gate_error"
  let rate1 (g : String) : Except String Rate := do
    let j ← (one.getObjVal? g).mapError fun _ => s!"calibration.one_qubit_gate_error: no `{g}`"
    Rate.ofList s!"one_qubit_gate_error.{g}" (← decimalValues s!"one_qubit_gate_error.{g}" j)
  let g2 := b.twoQubit
  let j2 ← (two.getObjVal? g2).mapError fun _ => s!"calibration.two_qubit_gate_error: no `{g2}`"
  let twoQubit ← Rate.ofList s!"two_qubit_gate_error.{g2}"
    (← decimalValues s!"two_qubit_gate_error.{g2}" j2)
  let readout ← Rate.ofList "readout_error"
    (← decimalValues "readout_error" (← field "calibration" cal "readout_error"))
  return { rz := ← rate1 "rz", sx := ← rate1 "sx", x := ← rate1 "x", twoQubit, readout }

/-! ## The weighted bound -/

/-- PHASE2_SPEC §C.1 — δ + Σ_types count · rate, with the rate of each type given by `pick`
(the worst or the median of its `Rate`); `readoutData` final readouts of the data register are
added to the measurements of the circuit (the IR carries no final readout), and the mid-circuit
measurements take the readout rate (the labelled assumption). Exact in ℚ. -/
def weightedBound (delta : Rat) (c : BasisCounts) (readoutData : Nat) (r : Rates)
    (pick : Rate → Rat) : Rat :=
  delta + c.rz * pick r.rz + c.sx * pick r.sx + c.x * pick r.x + c.twoQubit * pick r.twoQubit
    + (c.midMeas + c.finalMeas + readoutData) * pick r.readout

/-- The report of `cqr hw bound`: both figures and their parts. -/
structure BoundReport where
  basis : TargetBasis
  counts : BasisCounts
  /-- Final readouts of the data register, added to the circuit's measurements. -/
  readoutData : Nat
  rates : Rates
  delta : Rat
  worst : Rat
  median : Rat
  deriving Repr

def BoundReport.mk' (b : TargetBasis) (C : Circuit) (readoutData : Nat) (r : Rates)
    (delta : Rat) : BoundReport :=
  let c := basisCounts b C
  { basis := b, counts := c, readoutData, rates := r, delta,
    worst := weightedBound delta c readoutData r (·.worst),
    median := weightedBound delta c readoutData r (·.median) }

/-- The worst-case figure is vacuous when it reaches 1. -/
def BoundReport.vacuous (R : BoundReport) : Bool := 1 ≤ R.worst

/-- The coefficient of η_mid (the unknown mid-circuit measurement rate): the number of
mid-circuit measurements. -/
def BoundReport.etaMidCoeff (R : BoundReport) : Nat := R.counts.midMeas

/-- A rational as `num/den` (or `num` when the denominator is 1), the form the Python check
parses exactly. -/
def ratStr (q : Rat) : String :=
  if q.den = 1 then s!"{q.num}" else s!"{q.num}/{q.den}"

/-- A rational as a `Float` (for the printed median line only). -/
def ratFloat (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

end CQRV.Hardware
