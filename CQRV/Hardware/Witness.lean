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
* **`applyWitness`**: the reconstruction of 25a — the `order` entries become placement steps
  (`PStep`: a SWAP, placed gates, a routed block), run by `runSteps` from the initial layout
  (canonical logical position ↦ physical qubit): the relabeled basis gates, the SWAPs expanded by
  the table (inside a block, under the block's condition), the blocks processed with a local
  layout that must be restored and SWAPs composing to the identity on the whole register, every
  element and member consumed exactly once, the element order and each block's member order
  checked by `validReorder`, the initial layout injective, the final layout checked against the
  witness. Any mismatch is an error naming the entry. (`Circuit.wf` is Physlib-side, so
  well-formedness of the physical circuit is decided where it is needed.) `applyWitness_sound`
  (`CQRV.Hardware.WitnessSound`, 26b3) is the semantics.
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
  /-- physical clbit of each IR classical bit; `applyWitness` requires the identity `[0, …, k−1]`
  with `C.nBits ≤ k` (revision R15) -/
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

/-- A placement step: a routing SWAP of two physical qubits; logical basis gates to place under the
current layout; a routed block — its logical gates (the members, in the circuit's order) and its
physical gates, already placed. -/
inductive PStep where
  | swap (p q : ℕ)
  | place (gs : List BasisGate)
  | block (L P : List BasisGate)
  deriving Repr, DecidableEq, Inhabited

/-- PHASE2_SPEC §C.3 — the physical gates of a step list from a layout: a SWAP is expanded by the
table and updates the layout, placed gates are relabeled by the current layout, a block's physical
gates are appended as they are. The second component is the layout at the end. -/
def runSteps (b : TargetBasis) (n : ℕ) : List PStep → List ℕ → List BasisGate × List ℕ
  | [], lay => ([], lay)
  | .swap p q :: rest, lay =>
    let r := runSteps b n rest (swapLay lay p q)
    ((swapEntry b (.data p) (.data q)).gates ++ r.1, r.2)
  | .place gs :: rest, lay =>
    let r := runSteps b n rest lay
    (gs.map (BasisGate.map (layoutQ n lay)) ++ r.1, r.2)
  | .block _ P :: rest, lay =>
    let r := runSteps b n rest lay
    (P ++ r.1, r.2)

/-- The step of one block body entry: a member (its index checked, the condition stripped: the
block re-wraps it) or a SWAP of two distinct physical qubits of the register. -/
def blockEntryStep (N : ℕ) (T : List BasisGate) (members : List ℕ) : BlockEntry → Except String PStep
  | .gate k =>
    if members.contains k then
      match T[k]? with
      | some bg => pure (.place [bg.stripIf])
      | none => throw s!"block: gate {k} outside the translated list"
    else throw s!"block: gate {k} is not a member"
  | .swap p q =>
    if p = q then throw s!"block: swap {p} {p}"
    else if p < N ∧ q < N then pure (.swap p q)
    else throw s!"block: swap {p} {q} outside the register"

/-- A check with its error message. -/
def ensure (c : Bool) (msg : String) : Except String Unit := if c then pure () else throw msg

/-- The steps of a block body, in order. -/
def blockSteps (N : ℕ) (T : List BasisGate) (members : List ℕ) : List BlockEntry → Except String (List PStep)
  | [] => pure []
  | e :: es => do
    let s ← blockEntryStep N T members e
    let ss ← blockSteps N T members es
    pure (s :: ss)

/-- One block: its body as steps, the layout restored at the end, the SWAPs composing to the
identity on the whole physical register (the layout check alone sees only the logical positions),
every member used exactly once in a valid order. Returns the logical gates (the members, in the
circuit's order) and the physical gates, every one under the block's condition. -/
def applyBlock (b : TargetBasis) (n N : ℕ) (T : List BasisGate) (j : ℕ) (members : List ℕ)
    (body : List BlockEntry) (lay : List ℕ) : Except String (List BasisGate × List BasisGate) :=
  blockSteps N T members body >>= fun steps =>
  ensure ((runSteps b n steps lay).2 == lay) "block: the layout is not restored at the end of the block" >>= fun _ =>
  ensure ((runSteps b n steps (List.range N)).2 == List.range N)
    "block: the SWAPs do not compose to the identity on the physical register" >>= fun _ =>
  ensure (validReorder (fun k => (T.getD k default).qubits) (fun _ => []) members
      (body.filterMap fun e => match e with | .gate k => some k | .swap _ _ => none))
    "block: the member order is not a valid reordering" >>= fun _ =>
  pure (members.map (T.getD · default), (runSteps b n steps lay).1.map (BasisGate.ifBit j))

/-- The state of the fold over `order`: the layout, the elements consumed (in order), the steps. -/
structure ApplyState where
  lay : List ℕ
  taken : List Elem
  steps : List PStep

/-- One entry of `order`. -/
def orderStep (b : TargetBasis) (n N : ℕ) (T : List BasisGate) (els : List Elem) (w : Witness)
    (st : ApplyState) : OrderEntry → Except String ApplyState
  | .swap p q =>
    if p = q then throw s!"order: swap {p} {p}"
    else if p < N ∧ q < N then
      pure { st with lay := swapLay st.lay p q, steps := st.steps ++ [.swap p q] }
    else throw s!"order: swap {p} {q} outside the register"
  | .elem i =>
    match els[i]? with
    | none => throw s!"order: element {i} outside the translated circuit"
    | some el =>
      if st.taken.contains el then throw s!"order: element {i} taken twice"
      else match el with
        | .plain k =>
          match T[k]? with
          | some bg => pure { st with taken := st.taken ++ [el], steps := st.steps ++ [.place [bg]] }
          | none => throw s!"order: gate {k} outside the translated list"
        | .block j members =>
          match w.blocks.lookup i with
          | none => throw s!"order: block {i} has no body in the witness"
          | some body =>
            applyBlock b n N T j members body st.lay >>= fun LP =>
            pure { st with taken := st.taken ++ [el], steps := st.steps ++ [.block LP.1 LP.2] }

/-- PHASE2_SPEC §C.3 — **`applyWitness`**: the physical circuit (a basis-gate list on the compact
register of width `N`) reconstructed from the logical circuit and the witness, every check of the
Python reconstruction made explicit, and two it leaves implicit: the initial layout is injective
(a permutation of the logical positions into the register), and a block's SWAPs compose to the
identity on the whole register. `.ok` only when all pass (`applyWitness_sound`,
`CQRV.Hardware.WitnessSound`). -/
def applyWitness (b : TargetBasis) (C : Circuit) (w : Witness) (N : ℕ) :
    Except String (List BasisGate) :=
  ensure (w.basis == b) "witness: basis differs from the table's" >>= fun _ =>
  ensure (w.initial.length == C.nData + C.nAnc && w.nLogical == C.nData + C.nAnc)
    "witness: initial layout length differs from the logical register" >>= fun _ =>
  ensure (w.initial.all (· < N) && w.final.all (· < N)) "witness: a layout position outside the register" >>= fun _ =>
  ensure (decide w.initial.Nodup) "witness: the initial layout is not injective" >>= fun _ =>
  ensure (w.clbitMap == List.range w.clbitMap.length && decide (C.nBits ≤ w.clbitMap.length))
    "witness: the classical-bit map is not the identity on the circuit's bits" >>= fun _ =>
  w.order.foldlM (orderStep b C.nData N (translate b C) (elements b C) w) ⟨w.initial, [], []⟩ >>= fun st =>
  ensure (st.taken.length == (elements b C).length) "order: not every element is executed" >>= fun _ =>
  ensure (st.lay == w.final) "order: the final layout differs from the witness" >>= fun _ =>
  ensure (validReorder (Elem.qubits (translate b C)) (Elem.bits (translate b C)) (elements b C) st.taken)
    "order: not a valid reordering of the dependency queues" >>= fun _ =>
  pure (runSteps b C.nData st.steps w.initial).1

/-- The physical circuit of a reconstruction, as an IR circuit on the compact register. -/
def physCircuit (N : ℕ) (G : List BasisGate) : Circuit := ⟨N, G.flatMap BasisGate.expand⟩

end CQRV.Hardware
