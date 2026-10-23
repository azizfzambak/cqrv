module

public import CQRV.Circuit.Schedule
public import CQRV.Synthesis.TempAnd
public import CQRV.Synthesis.Network

/-!
# CQRV.Synthesis.Bennett

Report §6.1.3 (Eq. 3, Table 2) — Bennett's reversible pebble game on a chain of `L` AND nodes
(DECISIONS.md 2026-10-23, Stage 5 decision 3). Node `i` (0-based) is `AND(node i−1, x[i+1])`,
node 0 is `AND(x[0], x[1])`. Valid moves:

* `place i`: node `i` is unpebbled, its predecessor is pebbled (node 0: always), and fewer
  than `aMax` pebbles are down. Executes `TempLogicalAND` (4 T). The last node is placed
  exactly once; `Z` is applied on its ancilla right after (the phase flip of §6.1.4).
* `remove i`: node `i` is pebbled and so is its predecessor (the CZ fix-up of MBU needs both
  controls). Executes `UncomputeTempLogicalAND` (0 T).

A schedule starts and ends with no pebble and places the last node once. `pebbleChain`
returns one that minimizes the number of forward placements (= executed T / 4), found by a
0-1 breadth-first search over the `2^(L+1)` game states with moves tried in the fixed order
`place 0, …, place L−1, remove 0, …, remove L−1` (first found wins, so it is deterministic).
An infeasible budget is an error, never a circuit.
-/

@[expose] public section

namespace CQRV.Synthesis

/-- Report §6.1.3 — a pebble move on chain node `i` (0-based). -/
inductive Move where
  | place (i : Nat)
  | remove (i : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace Bennett

/-- The largest chain the search accepts (`2^(L+1)` states). -/
def maxChain : Nat := 16

/-- Game state: the pebbled nodes (bit `i` of `mask`) and whether the last node has been
placed (bit `L`). -/
abbrev GState := Nat

/-- Is bit `i` set? -/
def has (s i : Nat) : Bool := (s >>> i) % 2 == 1

/-- Number of pebbles down (bits `0..L`). -/
def pebbles (L s : Nat) : Nat := ((List.range L).filter (has s ·)).length

/-- Report §6.1.3, decision 3 — the successors of state `s`: `(move, next state, cost)`;
cost 1 for a placement, 0 for a removal. -/
def succ (L aMax s : Nat) : List (Move × Nat × Nat) :=
  let predOk (i : Nat) := i == 0 || has s (i - 1)
  let places := (List.range L).filterMap fun i =>
    if !has s i && predOk i && pebbles L s < aMax && !(i == L - 1 && has s L) then
      some (.place i, s + 2 ^ i + (if i == L - 1 then 2 ^ L else 0), 1)
    else none
  let removes := (List.range L).filterMap fun i =>
    if has s i && predOk i then some (.remove i, s - 2 ^ i, 0) else none
  places ++ removes

/-- One BFS level: close `stack` under cost-0 moves at distance `d`; returns the updated
`(dist, pred)` and every state of this level. `fuel` bounds the work. -/
def closeLevel (L aMax d : Nat) : Nat → List Nat → Array Nat → Array (Option (Nat × Move)) →
    List Nat → Array Nat × Array (Option (Nat × Move)) × List Nat
  | 0, _, dist, pred, acc => (dist, pred, acc)
  | _ + 1, [], dist, pred, acc => (dist, pred, acc)
  | fuel + 1, s :: stack, dist, pred, acc =>
    let (dist, pred, stack) := (succ L aMax s).foldl (fun (dist, pred, stack) (m, s', c) =>
      if c == 0 && dist.getD s' 0 > d then
        (dist.set! s' d, pred.set! s' (some (s, m)), s' :: stack)
      else (dist, pred, stack)) (dist, pred, stack)
    closeLevel L aMax d fuel stack dist pred (s :: acc)

/-- Follow the predecessor links back from `s` to the start state 0. -/
def path (pred : Array (Option (Nat × Move))) : Nat → Nat → List Move → List Move
  | 0, _, acc => acc
  | fuel + 1, s, acc =>
    match pred.getD s none with
    | some (p, m) => if s == 0 && p == 0 then acc else path pred fuel p (m :: acc)
    | none => acc

end Bennett

open Bennett in
/-- Report §6.1.3, decision 3 — a valid pebbling of a chain of `L` ANDs with at most `aMax`
pebbles that places the last node once and minimizes forward placements; an error when no
valid schedule exists. -/
def pebbleChain (L aMax : Nat) : Except String (List Move) := do
  if L == 0 then return []
  if L > maxChain then throw s!"pebbleChain: chains longer than {maxChain} are not supported"
  let V := 2 ^ (L + 1)
  let inf := V * (L + 1) + 1
  let goal := 2 ^ L
  let init : Array Nat × Array (Option (Nat × Move)) × List Nat × Bool :=
    ((Array.replicate V inf).set! 0 0, Array.replicate V none, [0], false)
  -- Level d holds the states at distance d (forward placements); at most V levels.
  let (dist, pred, _, _) := (List.range (V + 1)).foldl (fun (dist, pred, front, done) d =>
    if done || front.isEmpty then (dist, pred, front, done) else
    let (dist, pred, level) := closeLevel L aMax d (V * (2 * L + 1)) front dist pred []
    if dist.getD goal inf == d then (dist, pred, [], true) else
    let (dist, pred, next) := level.reverse.foldl (fun (dist, pred, next) s =>
      (succ L aMax s).foldl (fun (dist, pred, next) (m, s', c) =>
        if c == 1 && dist.getD s' inf == inf then
          (dist.set! s' (d + 1), pred.set! s' (some (s, m)), next ++ [s'])
        else (dist, pred, next)) (dist, pred, next)) (dist, pred, [])
    (dist, pred, next, false)) init
  if dist.getD goal inf == inf then
    throw s!"infeasible: no valid pebbling of a chain of {L} ANDs with {aMax} ancillae \
      (decision 3: place and remove need the predecessor pebbled; with p pebbles the farthest \
      node reachable is 2^p − 1)"
  -- The goal state is reached with predecessor links; rebuild the moves.
  return path pred (V * (L + 1)) goal []

namespace Bennett

/-- Number of forward placements of a schedule. -/
def placements (ms : List Move) : Nat := (ms.filter (· matches .place _)).length

/-- Report §6.1.3, Table 2 "Pebble rounds" as measured here: the largest number of times any
single node is placed (1 for the straight-line schedule). -/
def rounds (ms : List Move) : Nat :=
  ms.foldl (fun m mv => match mv with
    | .place i => Nat.max m (ms.filter (· == .place i)).length
    | .remove _ => m) 0

/-- Report §6.1.3 — the chain oracle of a schedule on `nData` data qubits; `lits` are the
`L + 1` chain operands (node 0 = `AND(x[lits₀], x[lits₁])`, node i = `AND(node i−1, x[litsᵢ₊₁])`).
`place i` = `alloc; TempLogicalAND(prev, x[litsᵢ₊₁], anc)`, plus `Z anc` after the last node;
`remove i` = MBU and `free`. Each placement takes the lowest free ancilla index; each
measurement a fresh classical bit. -/
def chainCircuit (nData : Nat) (lits : List Nat) (ms : List Move) : Circuit :=
  let L := lits.length - 1
  let lit (k : Nat) : Qubit := .data (lits.getD k 0)
  let prev (home : List (Nat × Nat)) (i : Nat) : Qubit :=
    if i == 0 then lit 0 else .anc ((home.lookup (i - 1)).getD 0)
  let (_, _, gs) := ms.foldl (fun (home, m, gs) mv =>
    match mv with
    | .place i =>
      let a := ((List.range (L + 1)).find? (fun a => !(home.map (·.2)).contains a)).getD 0
      let t := Qubit.anc a
      let gs := gs ++ [.alloc t] ++ TempLogicalAND (prev home i) (lit (i + 1)) t
      let gs := if i == L - 1 then gs ++ [.z t] else gs
      ((i, a) :: home, m, gs)
    | .remove i =>
      let a := (home.lookup i).getD 0
      let t := Qubit.anc a
      (home.filter (·.1 != i), m + 1,
        gs ++ UncomputeTempLogicalAND (prev home i) (lit (i + 1)) t m ++ [.free t]))
    (([] : List (Nat × Nat)), 0, ([] : List Gate))
  { nData, gates := gs }

/-- Report §6.1.3 — the operands of an AND chain, if the network is one: the output is the
last of `L ≥ 1` ANDs, node 0 = `AND(input, input)`, node i = `AND(node i−1, input)`, every
input positive, nothing else in the output's cone. Returns the `L + 1` input bits. -/
def chainOf (N : Network) : Option (List Nat) := do
  let [out] := N.outputs | none
  let input (i : Nat) : Option Nat :=
    match N.nodes[i]? with | some (.input k) => some k | _ => none
  -- Walk down the chain from the output.
  let rec walk : Nat → Nat → List Nat → Option (List Nat)
    | 0, _, _ => none
    | fuel + 1, k, acc =>
      match N.nodes[k]? with
      | some (.and i j) => do
        let b ← input j
        match input i with
        | some a => some (a :: b :: acc)
        | none => walk fuel i (b :: acc)
      | _ => none
  walk N.nodes.size out []

end Bennett

end CQRV.Synthesis

end
