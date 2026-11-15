module

public import CQRV.Hardware.Relabel
public import CQRV.Hardware.Target

/-!
# CQRV.Hardware.Witness

Report §5.3, §9.1.1; PHASE2_SPEC §C.3 step 3 (Stage 26b2, Track C) — the routing witness of
`hw/transpile.py` (`docs/hw_witness.schema.json`) in Lean, Physlib-free, and its reconstruction.

* **Dependency queues.** `indep` (disjoint qubits and disjoint classical bits) and `validReorder`:
  `gs'` is a valid reordering of `gs` when each of its elements, taken in turn, is independent of
  everything still before it in `gs` — the acceptance condition of the Python matcher
  (`witness_of`: an element is matched only at the head of every queue it touches). It is
  polymorphic in the element type, through the functions giving an element's qubits and bits;
  `CQRV.Hardware.Reorder` proves that it preserves the Kraus operators.
* **Elements.** The translated circuit (`translate b C`) grouped as the Python side groups it: one
  element per basis gate of an unconditioned IR gate, one block per conditioned IR gate
  (`elements`); element indices and block member indices are positions in `translate b C`, as in
  the witness.
* **`Witness`** and `Witness.ofJson`, with the compact remapping (physical qubit `p` of the device
  becomes its position in the manifest's `used_qubits`, so the physical register is `Reg N` with
  `N` the number of used qubits).
* **`applyWitness`**: the reconstruction of 25a — a fold over `order` with the current layout
  (canonical logical position ↦ physical qubit), the relabeled basis gates, the SWAPs expanded by
  the table (inside a block, under the block's condition), the blocks processed with a local
  layout that must be restored, every element and member consumed exactly once, the element order
  and each block's member order checked by `validReorder`, the final layout checked against the
  witness, and every physical qubit inside the compact register. Any mismatch is an error naming
  the entry. (`Circuit.wf` is Physlib-side, so well-formedness of the physical circuit is decided
  where it is needed, in `Reorder` / 26c.) `applyWitness_sound` (26b3) is the semantics.
-/

@[expose] public section

namespace CQRV.Hardware

open CQRV

/-! ## Dependency queues -/

/-- The classical bits a gate touches: the bit it writes (`measure`) or reads (`ifBit`). -/
def _root_.CQRV.Gate.bits : Gate → List ℕ
  | .measure _ j => [j]
  | .ifBit j _ => [j]
  | _ => []

/-- Two lists are disjoint. -/
def disjointL {α : Type} [DecidableEq α] (l₁ l₂ : List α) : Bool := l₁.all fun x => !decide (x ∈ l₂)

/-- Two elements are independent: disjoint qubits and disjoint classical bits. -/
def indep {α : Type} (qs : α → List Qubit) (bs : α → List ℕ) (x y : α) : Bool :=
  disjointL (qs x) (qs y) && disjointL (bs x) (bs y)

/-- Split off the first occurrence of `x`: the elements before it and after it. -/
def splitFirst {α : Type} [DecidableEq α] (x : α) : List α → Option (List α × List α)
  | [] => none
  | y :: ys => if y = x then some ([], ys) else (splitFirst x ys).map fun p => (y :: p.1, p.2)

/-- `validReorder qs bs l l'`: `l'` is `l` reordered so that each element, when taken, is at the
head of every dependency queue (qubits and bits) it touches — everything still before its first
occurrence in `l` is independent of it. -/
def validReorder {α : Type} [DecidableEq α] (qs : α → List Qubit) (bs : α → List ℕ) :
    List α → List α → Bool
  | l, [] => l.isEmpty
  | l, x :: rest =>
    match splitFirst x l with
    | some (pre, post) => pre.all (indep qs bs x) && validReorder qs bs (pre ++ post) rest
    | none => false

/-! ## The elements of the translated circuit -/

/-- An element of the translated circuit: a plain basis gate (its index in `translate b C`) or a
conditioned block (the bit, and the member indices). -/
inductive Elem where
  | plain (k : ℕ)
  | block (j : ℕ) (members : List ℕ)
  deriving Repr, DecidableEq, Inhabited

/-- The elements of `translate b C`, grouped as `hw/transpile.py` groups them. -/
def elements (b : TargetBasis) (C : Circuit) : List Elem :=
  go C.gates 0
where
  go : List Gate → ℕ → List Elem
    | [], _ => []
    | g :: gs, k =>
      let m := (decompTable b g).gates.length
      match g with
      | .ifBit j _ => .block j (List.range m |>.map (· + k)) :: go gs (k + m)
      | _ => (List.range m |>.map fun i => Elem.plain (i + k)) ++ go gs (k + m)

/-- The qubits of an element, from the translated gate list. -/
def Elem.qubits (T : List BasisGate) : Elem → List Qubit
  | .plain k => (T.getD k default).qubits
  | .block _ ms => ms.flatMap fun k => (T.getD k default).qubits

/-- The classical bits of an element. -/
def Elem.bits (T : List BasisGate) : Elem → List ℕ
  | .plain k => match T.getD k default with | .measure _ j => [j] | _ => []
  | .block j _ => [j]

/-! ## The witness -/

inductive OrderEntry where
  | elem (i : ℕ)
  | swap (p q : ℕ)
  deriving Repr, DecidableEq, Inhabited

inductive BlockEntry where
  | gate (k : ℕ)
  | swap (p q : ℕ)
  deriving Repr, DecidableEq, Inhabited

/-- The witness (`docs/hw_witness.schema.json`), as far as the reconstruction needs it, on the
compact register. -/
structure Witness where
  basis : TargetBasis
  nLogical : ℕ
  /-- physical qubit (compact) of each canonical logical position -/
  initial : List ℕ
  final : List ℕ
  order : List OrderEntry
  /-- block element index ↦ its body -/
  blocks : List (ℕ × List BlockEntry)
  clbitMap : List ℕ
  seed : ℕ
  deriving Repr

open Lean in
/-- A JSON array of natural numbers. -/
def natList (ctx : String) (j : Json) : Except String (List ℕ) := do
  (← j.getArr?.mapError fun _ => s!"{ctx}: not an array").toList.mapM fun x =>
    x.getNat?.mapError fun _ => s!"{ctx}: not a natural number"

/-- The compact remapping: a physical qubit of the device becomes its position in `used`. -/
def compactOf (used : List ℕ) (ctx : String) (p : ℕ) : Except String ℕ :=
  match used.idxOf? p with
  | some i => pure i
  | none => throw s!"{ctx}: physical qubit {p} is not a used qubit"

open Lean in
def OrderEntry.ofJson (used : List ℕ) (j : Json) : Except String OrderEntry := do
  match j.getObjVal? "e" with
  | .ok e => return .elem (← e.getNat?.mapError fun _ => "order: `e` must be a natural number")
  | .error _ =>
    let s ← natList "order.swap" (← field "order" j "swap")
    match s with
    | [p, q] => return .swap (← compactOf used "order.swap" p) (← compactOf used "order.swap" q)
    | _ => throw "order.swap: an edge has two endpoints"

open Lean in
def BlockEntry.ofJson (used : List ℕ) (j : Json) : Except String BlockEntry := do
  match j.getObjVal? "g" with
  | .ok g => return .gate (← g.getNat?.mapError fun _ => "blocks: `g` must be a natural number")
  | .error _ =>
    let s ← natList "blocks.swap" (← field "blocks" j "swap")
    match s with
    | [p, q] => return .swap (← compactOf used "blocks.swap" p) (← compactOf used "blocks.swap" q)
    | _ => throw "blocks.swap: an edge has two endpoints"

open Lean in
/-- PHASE2_SPEC §C.3 — a witness from its JSON, the device's physical qubits remapped to their
positions in `used` (the manifest's `layout.used_qubits`). -/
def Witness.ofJson (j : Json) (used : List ℕ) : Except String Witness := do
  let v ← strField "witness" j "schema_version"
  unless v == "1.0.0" do throw s!"witness: schema_version {v}, expected 1.0.0"
  let basis ← match ← strField "witness" j "basis" with
    | "cz" => pure TargetBasis.cz
    | "cx" => pure TargetBasis.cx
    | b => throw s!"witness: basis {b}"
  let nLogical ← natField "witness" j "n_logical"
  let initial ← (← natList "initial_layout" (← field "witness" j "initial_layout")).mapM
    (compactOf used "initial_layout")
  let final ← (← natList "final_layout" (← field "witness" j "final_layout")).mapM
    (compactOf used "final_layout")
  let order ← (← (← field "witness" j "order").getArr?.mapError fun _ => "order: not an array").toList.mapM
    (OrderEntry.ofJson used)
  let blocksObj ← (← field "witness" j "blocks").getObj?.mapError fun _ => "blocks: not an object"
  let blocks ← blocksObj.toList.mapM fun (k, body) => do
    let some i := k.toNat? | throw s!"blocks: key `{k}` is not an element index"
    let entries ← (← body.getArr?.mapError fun _ => s!"blocks.{k}: not an array").toList.mapM
      (BlockEntry.ofJson used)
    return (i, entries)
  let clbitMap ← natList "clbit_map" (← field "witness" j "clbit_map")
  let seed ← natField "witness" j "seed"
  return { basis, nLogical, initial, final, order, blocks, clbitMap, seed }

/-! ## The reconstruction -/

/-- The canonical position of a logical qubit: data `i` at `i`, ancilla `j` after the `n` data
qubits (`Qubit.place`). -/
def canonPos (n : ℕ) : Qubit → ℕ
  | .data i => i
  | .anc j => n + j

/-- The physical qubit of a logical qubit under a layout. -/
def layoutQ (n : ℕ) (lay : List ℕ) (q : Qubit) : Qubit := .data (lay.getD (canonPos n q) 0)

/-- The layout after a SWAP of physical qubits `p` and `q`. -/
def swapLay (lay : List ℕ) (p q : ℕ) : List ℕ :=
  lay.map fun x => if x = p then q else if x = q then p else x

/-- The gate inside a conditioned basis gate (the members of a block are stored conditioned in
`translate b C`; the reconstruction re-wraps them). -/
def BasisGate.stripIf : BasisGate → BasisGate
  | .ifBit _ g => g
  | g => g

/-- The physical basis gates of one block body entry; the local layout threaded. -/
def blockStep (b : TargetBasis) (n : ℕ) (j : ℕ) (T : List BasisGate) (members : List ℕ) :
    BlockEntry → List ℕ → Except String (List BasisGate × List ℕ)
  | .gate k, lay =>
    if members.contains k then
      match T[k]? with
      | some bg => pure ([.ifBit j (bg.stripIf.map (layoutQ n lay))], lay)
      | none => throw s!"block: gate {k} outside the translated list"
    else throw s!"block: gate {k} is not a member"
  | .swap p q, lay =>
    if p = q then throw s!"block: swap {p} {p}"
    else pure ((swapEntry b (.data p) (.data q)).gates.map (BasisGate.ifBit j), swapLay lay p q)

/-- One block: its body in order, with the local layout restored at the end and every member used
exactly once, in a valid order. -/
def applyBlock (b : TargetBasis) (n : ℕ) (T : List BasisGate) (j : ℕ) (members : List ℕ)
    (body : List BlockEntry) (lay : List ℕ) : Except String (List BasisGate) := do
  let (out, lay') ← body.foldlM (fun (acc : List BasisGate × List ℕ) e => do
    let (gs, lay') ← blockStep b n j T members e acc.2
    return (acc.1 ++ gs, lay')) ([], lay)
  unless lay' == lay do throw "block: the layout is not restored at the end of the block"
  let taken := body.filterMap fun e => match e with | .gate k => some k | .swap _ _ => none
  unless validReorder (fun k => (T.getD k default).qubits) (fun _ => []) members taken do
    throw "block: the member order is not a valid reordering"
  return out

/-- The state of the fold over `order`: the layout, the elements consumed (in order), the output. -/
structure ApplyState where
  lay : List ℕ
  taken : List Elem
  out : List BasisGate

/-- PHASE2_SPEC §C.3 — **`applyWitness`**: the physical circuit (a basis-gate list on the compact
register) reconstructed from the logical circuit and the witness, every check of the Python
reconstruction made explicit; `.ok` only when all pass. `N` is the width of the compact register. -/
def applyWitness (b : TargetBasis) (C : Circuit) (w : Witness) (N : ℕ) :
    Except String (List BasisGate) := do
  let n := C.nData
  let T := translate b C
  let els := elements b C
  unless w.basis == b do throw "witness: basis differs from the table's"
  unless w.initial.length == n + C.nAnc ∧ w.nLogical == n + C.nAnc do
    throw "witness: initial layout length differs from the logical register"
  unless w.initial.all (· < N) ∧ w.final.all (· < N) do throw "witness: a layout position outside the register"
  let st ← w.order.foldlM (fun (st : ApplyState) e => do
    match e with
    | .swap p q =>
      if p = q then throw s!"order: swap {p} {p}"
      return { st with lay := swapLay st.lay p q,
                       out := st.out ++ (swapEntry b (.data p) (.data q)).gates }
    | .elem i =>
      match els[i]? with
      | none => throw s!"order: element {i} outside the translated circuit"
      | some el =>
        if st.taken.contains el then throw s!"order: element {i} taken twice"
        match el with
        | .plain k =>
          match T[k]? with
          | some bg => return { st with taken := st.taken ++ [el], out := st.out ++ [bg.map (layoutQ n st.lay)] }
          | none => throw s!"order: gate {k} outside the translated list"
        | .block j members =>
          match w.blocks.lookup i with
          | none => throw s!"order: block {i} has no body in the witness"
          | some body =>
            let gs ← applyBlock b n T j members body st.lay
            return { st with taken := st.taken ++ [el], out := st.out ++ gs })
    ⟨w.initial, [], []⟩
  unless st.taken.length == els.length do throw "order: not every element is executed"
  unless st.lay == w.final do throw "order: the final layout differs from the witness"
  unless validReorder (Elem.qubits T) (Elem.bits T) els st.taken do
    throw "order: not a valid reordering of the dependency queues"
  unless (st.out.flatMap BasisGate.expand).all fun g => g.qubits.all fun q =>
      match q with | .data i => decide (i < N) | .anc _ => false do
    throw "the reconstructed physical circuit has a qubit outside the compact register"
  return st.out

/-- The physical circuit of a reconstruction, as an IR circuit on the compact register. -/
def physCircuit (N : ℕ) (G : List BasisGate) : Circuit := ⟨N, G.flatMap BasisGate.expand⟩

end CQRV.Hardware
