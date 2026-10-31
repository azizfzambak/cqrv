module

public import Lean.Data.Json

/-!
# CQRV.Circuit.IR

Report §6.1.4, §6.2.2, §9.1.1 — the gate-level IR of the synthesizer: Clifford+T gates,
computational-basis measurement into a classical bit, classically controlled Clifford gates
(the MBU fix-up of §6.2.2), and ancilla `alloc`/`free`. A circuit acts on a data register
`x[0..nData)` and on named ancillae `anc[i]`. Stage 17a (PHASE2_SPEC.md §A.1) adds the exact
phase gates `p a k` = diag(1, e^{2πi·a/2^k}) and the controlled `cp a k` (`a : Int`, `k : Nat`;
no floating point in the IR) and the classifiers `isTPower`, `isRotation`, `isTwoQubit` behind the
second record `GradeExt`; no synthesized circuit contains them (they are infrastructure for
Stages 18–20).

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
`alloc q` / `free q` bracket the lifetime of an ancilla (it must be |0⟩ at both ends).
PHASE2_SPEC.md §A.1 (Stage 17a): `p a k q` is the exact phase gate `diag(1, exp(2πi·a/2^k))` on
`q` and `cp a k c t` applies that phase to the states where `c` and `t` both read 1 (as `cz`
does with −1); `a : Int` may be negative (the adjoint is `p (-a) k`). -/
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
  | p (a : Int) (k : Nat) (q : Qubit)
  | cp (a : Int) (k : Nat) (c t : Qubit)
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
  | .h q | .s q | .sdg q | .t q | .tdg q | .x q | .z q | .measure q _ | .alloc q | .free q
  | .p _ _ q => [q]
  | .cnot a b | .cz a b | .cp _ _ a b => [a, b]
  | .ifBit _ g => g.qubits

/-- Report §6.2.2 — the unitary Clifford gates (allowed under `ifBit`). PHASE2_SPEC.md §A.1:
`p a k` is Clifford iff its angle is a multiple of π/2, i.e. `2^k ∣ 4a`; `cp a k` iff its angle
is a multiple of π, i.e. `2^k ∣ 2a` (`cp 1 1 = cz`, `cp 2 2 = cz`, `cp 0 k = 1`). -/
def isClifford : Gate → Bool
  | .h _ | .s _ | .sdg _ | .x _ | .z _ | .cnot _ _ | .cz _ _ => true
  | .p a k _ => decide ((2 ^ k : Int) ∣ 4 * a)
  | .cp a k _ _ => decide ((2 ^ k : Int) ∣ 2 * a)
  | _ => false

/-- PHASE2_SPEC.md §A.1 (Stage 17a) — a T or T† up to Clifford: `t`, `tdg`, and a `p a k` whose
angle is an odd multiple of π/4, i.e. `2^k ∣ 8a` and not `2^k ∣ 4a` (`p 1 3`, `p (-1) 3`, `p 3 3`,
`p 2 4`, … count exactly as `t` / `tdg`; a divisibility condition, not "`k = 3` and `a` odd",
DECISIONS.md 2026-10-31); `ifBit` looks inside; `cp` is never a T-power. -/
def isTPower : Gate → Bool
  | .t _ | .tdg _ => true
  | .p a k _ => decide ((2 ^ k : Int) ∣ 8 * a) && !decide ((2 ^ k : Int) ∣ 4 * a)
  | .ifBit _ g => g.isTPower
  | _ => false

/-- Report §6.1.2 — number of T and T† gates in one gate; PHASE2_SPEC.md §A.1: a T-power `p a k`
counts 1 (`tCount_eq_isTPower`), `cp` counts 0. -/
def tCount : Gate → Nat
  | .t _ | .tdg _ => 1
  | .p a k _ => if decide ((2 ^ k : Int) ∣ 8 * a) && !decide ((2 ^ k : Int) ∣ 4 * a) then 1 else 0
  | .ifBit _ g => g.tCount
  | _ => 0

/-- PHASE2_SPEC.md §A.1 — `tCount` is the indicator of `isTPower`. -/
theorem tCount_eq_isTPower (g : Gate) : g.tCount = if g.isTPower then 1 else 0 := by
  induction g with
  | ifBit _ g ih => simp only [tCount, isTPower]; exact ih
  | _ => simp [tCount, isTPower]

/-- PHASE2_SPEC.md §A.1, §A.8 item 2 (Stage 17a) — a rotation: a `p` / `cp` gate that is neither
Clifford nor a T-power (`p a k` with `2^k ∤ 8a`; `cp a k` with `2^k ∤ 2a`), whose Clifford+T cost
depends on a synthesis precision (PHASE2_SPEC.md §C) and is counted in `GradeExt.rot`, not in
`t`; `false` for every other constructor; `ifBit` looks inside. -/
def isRotation : Gate → Bool
  | .p a k _ => !decide ((2 ^ k : Int) ∣ 8 * a)
  | .cp a k _ _ => !decide ((2 ^ k : Int) ∣ 2 * a)
  | .ifBit _ g => g.isRotation
  | _ => false

/-- PHASE2_SPEC.md §A.1 (Stage 17a) — the two-qubit gates `cnot`, `cz`, `cp` (`ifBit` looks
inside), counted in `GradeExt.twoQ`. -/
def isTwoQubit : Gate → Bool
  | .cnot _ _ | .cz _ _ | .cp _ _ _ _ => true
  | .ifBit _ g => g.isTwoQubit
  | _ => false

/-- PHASE2_SPEC.md §A.1 (Stage 17a) — a `measure` gate (`GradeExt.meas`). -/
def isMeasure : Gate → Bool
  | .measure _ _ => true
  | _ => false

/-- PHASE2_SPEC.md §A.1 (Stage 17a) — a classically controlled gate (`GradeExt.ff`). -/
def isIfBit : Gate → Bool
  | .ifBit _ _ => true
  | _ => false

/-- PHASE2_SPEC.md §A.0.1 (extends report §6.2.2) — the adjoint of a unitary gate: `s ↔ sdg`,
`t ↔ tdg`; `h`, `x`, `z`, `cnot`, `cz` are self-adjoint; `p a k ↦ p (-a) k`, `cp a k ↦ cp (-a) k`
(PHASE2_SPEC.md §A.1). `measure`, `ifBit`, `alloc`, `free` are returned unchanged (the function
is total; the semantic theorems assume `Gate.isUnitary`, `CQRV.Circuit.Semantics`). -/
def adjoint : Gate → Gate
  | .s q => .sdg q
  | .sdg q => .s q
  | .t q => .tdg q
  | .tdg q => .t q
  | .p a k q => .p (-a) k q
  | .cp a k c tg => .cp (-a) k c tg
  | g => g

/-- Report §6.2.2, §9.1.1 — shift the classical bits of a gate up by `k` (`measure q → j` writes
`j + k`, `ifBit j g` reads `j + k`); used by `Circuit.append` and by the synthesizer, which numbers
bits in measurement order (DECISIONS.md, Stage 6b-1 review). -/
def shiftBits (k : Nat) : Gate → Gate
  | .measure q j => .measure q (j + k)
  | .ifBit j g => .ifBit (j + k) g
  | g => g

/-- The classical bits a gate writes (`measure q → j` writes `j`). -/
def writes : Gate → List Nat
  | .measure _ j => [j]
  | _ => []

/-- Readable form, as in the §6.1.4 / §6.2.2 listings (used by the layer dump). `p` / `cp` print
their angle as the fraction `a/2^k` of a full turn (`P(1/8) x[0]` is `T x[0]`), both numbers as
integers. -/
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
  | .p a k q => s!"P({a}/{2 ^ k}) {q.render}"
  | .cp a k c tg => s!"CP({a}/{2 ^ k}) {c.render} {tg.render}"

end Gate

/-- PHASE2_SPEC.md §A.0.1 — the adjoint of a measurement-free gate list: the adjoint gates in
reverse order (`(g₁ ⋯ gₖ)† = gₖ† ⋯ g₁†`); `unitaryDenote_adjoint` in `Semantics`. -/
def adjointGates (gs : List Gate) : List Gate := (gs.map Gate.adjoint).reverse

namespace Circuit

/-- The classical bits written by a gate list, in program order. -/
def written (gs : List Gate) : List Nat := gs.flatMap Gate.writes

/-- Report §9.1.1 — the number of classical bits: one per `measure`. -/
def nBits (C : Circuit) : Nat := (written C.gates).length

/-- Report §6.2.2, §9.1.1 — sequential composition with shifted classical bits: the gates of
`C₁`, then those of `C₂` with every classical bit shifted up by `C₁.nBits`, so the bits of the
two pieces never clash (DECISIONS.md, Stage 6b-1 review, (A); moved here from
`CQRV.Circuit.Semantics` in Stage 5b). The register is `C₁`'s. -/
def append (C₁ C₂ : Circuit) : Circuit :=
  ⟨C₁.nData, C₁.gates ++ C₂.gates.map (Gate.shiftBits C₁.nBits)⟩

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
    | .cnot a b | .cz a b | .cp _ _ a b => if a == b then throw s!"`{g.render}`: repeated qubit"
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

/-- One gate as a flat JSON object `{op, q, c?, a?, k?, if?}` (`q`: flat qubit indices; `a` a JSON
integer, possibly negative, and `k` a natural for `p` / `cp`, PHASE2_SPEC.md §A.1). -/
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
      | .p _ _ _ => "p" | .cp _ _ _ _ => "cp"
    let base := [("op", toJson op), ("q", toJson (g.qubits.map c.qIndex))]
    match g with
    | .measure _ k => Json.mkObj (base ++ [("c", toJson k)])
    | .p a k _ | .cp a k _ _ => Json.mkObj (base ++ [("a", toJson a), ("k", toJson k)])
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
