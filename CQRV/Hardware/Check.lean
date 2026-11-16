module

public import CQRV.Hardware.Witness

/-!
# CQRV.Hardware.Check

Report §5.3, §9.1.1; PHASE2_SPEC §C.3 (Stage 26c1, Track C) — the per-instance checks the kernel
can afford, Physlib-free.

* **`applyWitnessQ`** (L1): the reconstruction of `applyWitness` with the dependency queues of the
  Python matcher in place of `validReorder` and the `taken` list — one queue per wire (a canonical
  qubit position, or a classical bit after the `n + a` positions), holding the elements on that
  wire in the circuit's order; an element may be taken when it is at the head of every queue of
  its wires, and taking it pops them; at the end every queue is empty. Nothing is indexed by the
  element count: an element is found through the heads of the queues (`findHead`), the queues are
  indexed by wire (`W = n + a + nBits` of them), and the steps are accumulated in reverse.
  `applyWitnessQ_ok` (`CQRV.Hardware.CheckSound`): `applyWitnessQ b C w N = .ok G →
  applyWitness b C w N = .ok G`, so `applyWitness_sound` applies unchanged.
-/

@[expose] public section

namespace CQRV.Hardware

open CQRV

/-! ## Wires and queues -/

/-- A list without repetitions (membership kept). -/
def dedup : List ℕ → List ℕ
  | [] => []
  | x :: xs => let r := dedup xs; if x ∈ r then r else x :: r

/-- The wires of an element: the canonical positions of its qubits (below `k = n + a`) and its
classical bits (at `k + j`), without repetition. -/
def Elem.wires (n k : ℕ) (T : List BasisGate) (e : Elem) : List ℕ :=
  dedup ((Elem.qubits T e).map (canonPos n) ++ (Elem.bits T e).map (· + k))

/-- A queue entry: the element's index in `elements b C`, the element, its wires, its basis gates. -/
abbrev QEntry := ℕ × Elem × List ℕ × List BasisGate

/-- The number of translated gates of an element. -/
def Elem.size : Elem → ℕ
  | .plain _ => 1
  | .block _ ms => ms.length

/-- The classical bits of an element, from its gates (`Elem.bits` from the gates themselves). -/
def Elem.bitsOf : Elem → List BasisGate → List ℕ
  | .plain _, gs => match gs with | [.measure _ j] => [j] | _ => []
  | .block j _, _ => [j]

/-- The wires of an element from its gates (`Elem.wires` without indexing the translation). -/
def wiresOf (n k : ℕ) (e : Elem) (gs : List BasisGate) : List ℕ :=
  dedup ((gs.flatMap BasisGate.qubits).map (canonPos n) ++ (Elem.bitsOf e gs).map (· + k))

/-- The elements with their indices (from `i`), wires and gates, **in one pass over the elements
and the translated gates together**: an element takes its gates from the front of `T` (the
elements enumerate `T` in order), so nothing is indexed by position — the kernel's cost stays
linear (26b3's probe: indexing `T` per element is quadratic in its cache). -/
def indexedWires (n k : ℕ) : List Elem → List BasisGate → ℕ → List QEntry
  | [], _, _ => []
  | e :: es, T, i =>
    (i, e, wiresOf n k e (T.take e.size), T.take e.size) :: indexedWires n k es (T.drop e.size) (i + 1)

/-- The queues: for each wire below `W`, the entries on that wire, in order. -/
def queuesOf (W : ℕ) (ents : List QEntry) : List (List QEntry) :=
  (List.range W).map fun w => ents.filter fun p => decide (w ∈ p.2.2.1)

def modifyAt {α : Type} (f : α → α) : ℕ → List α → List α
  | _, [] => []
  | 0, x :: xs => f x :: xs
  | i + 1, x :: xs => x :: modifyAt f i xs

/-- The entry of index `i` at the head of some queue. -/
def findHead (Q : List (List QEntry)) (i : ℕ) : Option QEntry :=
  Q.findSome? fun q => match q with
    | p :: _ => if p.1 = i then some p else none
    | [] => none

/-- Every queue of the wires `ws` has an entry of index `i` at its head. -/
def headsAre (Q : List (List QEntry)) (i : ℕ) (ws : List ℕ) : Bool :=
  ws.all fun w => match Q.getD w [] with
    | p :: _ => p.1 == i
    | [] => false

/-- Pop the head of every queue of the wires `ws`. -/
def popAll (ws : List ℕ) (Q : List (List QEntry)) : List (List QEntry) :=
  ws.foldl (fun Q w => modifyAt List.tail w Q) Q

/-! ## The linear reconstruction -/

/-- The state of the queue fold: the layout, the queues, the steps in reverse. -/
structure QState where
  lay : List ℕ
  Q : List (List QEntry)
  stepsRev : List PStep

/-- One entry of `order`, with the queues. -/
def orderStepQ (b : TargetBasis) (n N : ℕ) (T : List BasisGate) (w : Witness) (st : QState) :
    OrderEntry → Except String QState
  | .swap p q =>
    if p = q then throw s!"order: swap {p} {p}"
    else if p < N ∧ q < N then
      pure { st with lay := swapLay st.lay p q, stepsRev := .swap p q :: st.stepsRev }
    else throw s!"order: swap {p} {q} outside the register"
  | .elem i =>
    match findHead st.Q i with
    | none => throw s!"order: element {i} is not at the head of any queue"
    | some (_, el, ws, gs) =>
      if headsAre st.Q i ws then
        match el with
        | .plain _ => pure { st with Q := popAll ws st.Q, stepsRev := .place gs :: st.stepsRev }
        | .block j members =>
          match w.blocks.lookup i with
          | none => throw s!"order: block {i} has no body in the witness"
          | some body =>
            applyBlock b n N T j members body st.lay >>= fun LP =>
            pure { st with Q := popAll ws st.Q, stepsRev := .block LP.1 LP.2 :: st.stepsRev }
      else throw s!"order: element {i} is not at the head of every queue of its wires"

/-- The queue fold with all its checks; the final state (the layout, the empty queues, the steps in
reverse). `applyWitnessQ` runs the steps; `finalPerm` names the final layout permutation. -/
def applyWitnessQ' (b : TargetBasis) (C : Circuit) (w : Witness) (N : ℕ) : Except String QState :=
  ensure (w.basis == b) "witness: basis differs from the table's" >>= fun _ =>
  ensure (w.initial.length == C.nData + C.nAnc && w.nLogical == C.nData + C.nAnc)
    "witness: initial layout length differs from the logical register" >>= fun _ =>
  ensure (w.initial.all (· < N) && w.final.all (· < N)) "witness: a layout position outside the register" >>= fun _ =>
  ensure (decide w.initial.Nodup) "witness: the initial layout is not injective" >>= fun _ =>
  ensure ((indexedWires C.nData (C.nData + C.nAnc) (elements b C) (translate b C) 0).all fun p =>
      p.2.2.1.all (· < C.nData + C.nAnc + C.nBits)) "witness: a wire outside the register" >>= fun _ =>
  w.order.foldlM (orderStepQ b C.nData N (translate b C) w)
    ⟨w.initial, queuesOf (C.nData + C.nAnc + C.nBits)
      (indexedWires C.nData (C.nData + C.nAnc) (elements b C) (translate b C) 0), []⟩ >>= fun st =>
  ensure (st.Q.all List.isEmpty) "order: not every element is executed" >>= fun _ =>
  ensure (st.lay == w.final) "order: the final layout differs from the witness" >>= fun _ =>
  pure st

/-- PHASE2_SPEC §C.3 (26c1 L1) — **`applyWitnessQ`**: `applyWitness` with the dependency queues;
`applyWitnessQ_ok` says it implies `applyWitness`. -/
def applyWitnessQ (b : TargetBasis) (C : Circuit) (w : Witness) (N : ℕ) :
    Except String (List BasisGate) :=
  applyWitnessQ' b C w N >>= fun st => pure (runSteps b C.nData st.stepsRev.reverse w.initial).1

/-- The steps of a successful reconstruction (`[]` otherwise). -/
def stepsOf (b : TargetBasis) (C : Circuit) (w : Witness) (N : ℕ) : List PStep :=
  match applyWitnessQ' b C w N with
  | .ok st => st.stepsRev.reverse
  | .error _ => []

/-! ## L3: the coupling check -/

/-- The compact qubit pair of a two-qubit basis gate (`ifBit` looked inside): `none` for a one-qubit
gate, `some none` for a two-qubit gate with a non-data operand (which fails the check). -/
def BasisGate.pairOf : BasisGate → Option (Option (ℕ × ℕ))
  | .cz (.data p) (.data q) => some (some (p, q))
  | .cx (.data p) (.data q) => some (some (p, q))
  | .cz _ _ => some none
  | .cx _ _ => some none
  | .ifBit _ g => g.pairOf
  | _ => none

/-- The two-qubit gates of a basis-gate list, as pairs of compact qubit indices. -/
def twoQubitPairs (G : List BasisGate) : List (Option (ℕ × ℕ)) := G.filterMap BasisGate.pairOf

/-- PHASE2_SPEC §C.3 (26c1 L3) — **`edgesOk`**: every two-qubit gate of `G`, mapped through the
compact → device list `dev`, lies on an edge of the target, in either orientation. -/
def edgesOk (G : List BasisGate) (dev : List ℕ) (edges : List (ℕ × ℕ)) : Bool :=
  (twoQubitPairs G).all fun o => match o with
    | some (p, q) =>
      p < dev.length && q < dev.length &&
        (edges.contains (dev.getD p 0, dev.getD q 0) || edges.contains (dev.getD q 0, dev.getD p 0))
    | none => false

end CQRV.Hardware
