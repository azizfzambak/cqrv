module

public import Lean.Data.Json

/-!
# CQRV.Circuit.IR

Report §6.1.4, §6.2.2, §9.1.1 — the gate-level IR of the synthesizer: Clifford+T gates,
computational-basis measurement into a classical bit, classically controlled Clifford gates
(the MBU fix-up of §6.2.2), and ancilla `alloc`/`free`. A circuit acts on a data register
`x[0..nData)` and on named ancillae `anc[i]`.

The denotational semantics (into Physlib channels) is Stage 6; here the IR is only scheduled
(`CQRV.Circuit.Schedule`), exported as JSON, and executed by the Python harness (`tests/diff/`).
-/

@[expose] public section

namespace CQRV

open Lean

/-- Report §6.1.4 — a qubit: data register `x[i]` or ancilla `anc[i]`. -/
inductive Qubit where
  | data (i : Nat)
  | anc (i : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Report §6.1.4 — the listing's name of a qubit (`x[3]`, `anc[0]`). -/
def Qubit.render : Qubit → String
  | .data i => s!"x[{i}]"
  | .anc i => s!"anc[{i}]"

/-- Canonical order of qubits: data before ancillae, then by index. -/
def Qubit.key : Qubit → Nat × Nat
  | .data i => (0, i)
  | .anc i => (1, i)

/-- Report §6.2.2, §9.1.1 — gates of the IR. `measure q c` measures `q` in the computational
basis into the classical bit `c`; `ifBit c g` applies the Clifford gate `g` when bit `c` is 1;
`alloc q` / `free q` bracket the lifetime of an ancilla (it must be |0⟩ at both ends). -/
inductive Gate where
  | h (q : Qubit)
  | s (q : Qubit)
  | sdg (q : Qubit)
  | t (q : Qubit)
  | tdg (q : Qubit)
  | x (q : Qubit)
  | z (q : Qubit)
  | cnot (c tgt : Qubit)
  | cz (a b : Qubit)
  | measure (q : Qubit) (c : Nat)
  | ifBit (c : Nat) (g : Gate)
  | alloc (q : Qubit)
  | free (q : Qubit)
  deriving Repr, DecidableEq, Inhabited

/-- Report §6.1.4 — a circuit: a gate list over `x[0..nData)` and ancillae `anc[i]`. The data
register size is part of the circuit because untouched data qubits count in the width
(DECISIONS.md 2026-10-23, Stage 5 interpretations (1)). -/
structure Circuit where
  nData : Nat
  gates : List Gate
  deriving Repr, DecidableEq, Inhabited

namespace Gate

/-- Qubits a gate acts on (for `ifBit`, those of the controlled gate). -/
def qubits : Gate → List Qubit
  | .h q | .s q | .sdg q | .t q | .tdg q | .x q | .z q | .measure q _ | .alloc q | .free q => [q]
  | .cnot a b | .cz a b => [a, b]
  | .ifBit _ g => g.qubits

/-- Report §6.2.2 — the unitary Clifford gates (allowed under `ifBit`). -/
def isClifford : Gate → Bool
  | .h _ | .s _ | .sdg _ | .x _ | .z _ | .cnot _ _ | .cz _ _ => true
  | _ => false

/-- Report §6.1.2 — number of T and T† gates in one gate. -/
def tCount : Gate → Nat
  | .t _ | .tdg _ => 1
  | .ifBit _ g => g.tCount
  | _ => 0

/-- Report §6.2.2, §9.1.1 — shift the classical bits of a gate up by `k` (`measure q → j` writes
`j + k`, `ifBit j g` reads `j + k`); used by `Circuit.append` and by the synthesizer, which numbers
bits in measurement order (DECISIONS.md, Stage 6b-1 review). -/
def shiftBits (k : Nat) : Gate → Gate
  | .measure q j => .measure q (j + k)
  | .ifBit j g => .ifBit (j + k) g
  | g => g

/-- Readable form, as in the §6.1.4 / §6.2.2 listings (used by the layer dump). -/
def render : Gate → String
  | .h q => s!"H {q.render}"
  | .s q => s!"S {q.render}"
  | .sdg q => s!"S† {q.render}"
  | .t q => s!"T {q.render}"
  | .tdg q => s!"T† {q.render}"
  | .x q => s!"X {q.render}"
  | .z q => s!"Z {q.render}"
  | .cnot a b => s!"CNOT {a.render} {b.render}"
  | .cz a b => s!"CZ {a.render} {b.render}"
  | .measure q c => s!"measure {q.render} → c{c}"
  | .ifBit c g => s!"if c{c}: {g.render}"
  | .alloc q => s!"alloc {q.render}"
  | .free q => s!"free {q.render}"

end Gate

namespace Circuit

/-- Ancilla indices used by the circuit (one more than the largest). -/
def nAnc (c : Circuit) : Nat :=
  c.gates.foldl (fun m g => g.qubits.foldl
    (fun m q => match q with | .anc i => Nat.max m (i + 1) | .data _ => m) m) 0

/-- Report §6.2.2, §9.1.1 — static well-formedness: data indices in range; two-qubit gates on
distinct qubits; `ifBit` wraps a Clifford gate and reads a bit measured earlier; every gate on
an ancilla lies between its `alloc` and `free` (no double `alloc`, no `free` of a dead ancilla);
every ancilla is freed at the end. -/
def validate (c : Circuit) : Except String Unit := do
  let mut live : List Nat := []
  let mut bits : List Nat := []
  for g in c.gates do
    let g' := match g with | .ifBit _ h => h | h => h
    if let .ifBit k _ := g then
      if !g'.isClifford then throw s!"`{g.render}`: classically controlled gate is not Clifford"
      if !bits.contains k then throw s!"`{g.render}`: bit c{k} read before it is measured"
    match g' with
    | .cnot a b | .cz a b => if a == b then throw s!"`{g.render}`: repeated qubit"
    | _ => pure ()
    for q in g.qubits do
      match q with
      | .data i => if i ≥ c.nData then throw s!"`{g.render}`: data qubit out of range"
      | .anc i =>
        match g with
        | .alloc _ =>
          if live.contains i then throw s!"`{g.render}`: ancilla already allocated"
          live := i :: live
        | .free _ =>
          if !live.contains i then throw s!"`{g.render}`: ancilla not allocated"
          live := live.erase i
        | _ => if !live.contains i then throw s!"`{g.render}`: ancilla used outside alloc/free"
    if let .measure _ k := g then bits := k :: bits
  if !live.isEmpty then throw s!"ancillae {live.reverse} are never freed"

/-- Flat index of a qubit in the JSON export: `x[i] ↦ i`, `anc[i] ↦ nData + i`. -/
def qIndex (c : Circuit) : Qubit → Nat
  | .data i => i
  | .anc i => c.nData + i

/-- One gate as a flat JSON object `{op, q, c?, if?}` (`q`: flat qubit indices). -/
def gateJson (c : Circuit) : Gate → Json
  | .ifBit k g =>
    match gateJson c g with
    | .obj kvs => .obj (kvs.insert "if" (toJson k))
    | j => j
  | g =>
    let op := match g with
      | .h _ => "h" | .s _ => "s" | .sdg _ => "sdg" | .t _ => "t" | .tdg _ => "tdg"
      | .x _ => "x" | .z _ => "z" | .cnot _ _ => "cnot" | .cz _ _ => "cz"
      | .measure _ _ => "measure" | .alloc _ => "alloc" | .free _ => "free" | .ifBit _ _ => "if"
    let base := [("op", toJson op), ("q", toJson (g.qubits.map c.qIndex))]
    match g with
    | .measure _ k => Json.mkObj (base ++ [("c", toJson k)])
    | _ => Json.mkObj base

/-- The flat export read by `tests/diff/statevector.py`:
`{n_data, n_anc, gates: [{op, q: [i…], c?, if?}]}`; data qubits are `0..n_data`, ancillae
follow. -/
def toJson (c : Circuit) : Json :=
  Json.mkObj
    [("n_data", Lean.toJson c.nData), ("n_anc", Lean.toJson c.nAnc),
     ("gates", Json.arr (c.gates.map (gateJson c)).toArray)]

end Circuit

end CQRV

end
