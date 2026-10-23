module

import CQRV.DSL.Basic
import CQRV.Synthesis.Basic
meta import CQRV.DSL.Basic
meta import CQRV.Synthesis.Basic

/-!
# Tests for `CQRV.Circuit` and `CQRV.Synthesis` (report §6.1.2–6.1.4, §6.2.2, §6.3.1)

Gate counts of the §6.2.2 listing, ĉ∧ = AND count of `toNetwork` on the corpus, the
decision-4 scheduler, the measured grade of the Grover oracle (Table 3) and the Table 2 rows
of the c∧ = 8 chain. Every number the report gives is checked as a claim; where it does not
hold, the test asserts the measured value and DECISIONS.md (2026-10-23, Stage 5) records why.
Semantic correctness of the circuits is checked by the Python harness (`tests/diff/`).
-/

namespace CQRV.Tests.Synthesis

open CQRV CQRV.DSL CQRV.Synthesis

/-! ## §6.2.2 — TempLogicalAND: 4 T to compute, 0 T to uncompute -/

def a : Qubit := .data 0
def b : Qubit := .data 1
def t : Qubit := .anc 0

#guard (TempLogicalAND a b t).foldl (· + ·.tCount) 0 == 4
#guard (UncomputeTempLogicalAND a b t 0).foldl (· + ·.tCount) 0 == 0
#guard (TempLogicalAND a b t).length == 13
-- The erratum fix: the uncompute ends with the classically controlled X that resets the target.
#guard UncomputeTempLogicalAND a b t 0 ==
  [.h t, .measure t 0, .ifBit 0 (.cz a b), .ifBit 0 (.x t)]

/-- The compute phase alone, on a fresh ancilla. -/
def andOnly : Circuit := ⟨2, [.alloc t] ++ TempLogicalAND a b t⟩
/-- Compute + uncompute. -/
def andPair : Circuit :=
  ⟨2, [.alloc t] ++ TempLogicalAND a b t ++ UncomputeTempLogicalAND a b t 0 ++ [.free t]⟩

-- Table 3 counts "7 each" for the compute phase; the listing has 11 gates on the target, so
-- no schedule fits it in fewer than 11 layers. Uncompute: 3 layers (both fixes share one).
#guard ((TempLogicalAND a b t).filter (t ∈ ·.qubits)).length == 11
#guard andOnly.depth == 11
#guard andPair.depth == 14
#guard andPair.validate.isOk
#guard (Circuit.mk 2 (TempLogicalAND a b t)).validate.isOk == false  -- no alloc

/-! ## Decision 4 — the scheduler -/

-- ASAP on disjoint qubits: one layer; alloc/free take none.
#guard (Circuit.mk 2 [.alloc t, .h a, .h b, .h t, .measure t 0, .free t]).depth == 2
-- A classically controlled gate waits for its measurement even on other qubits.
#guard (Circuit.mk 2 [.alloc t, .measure t 0, .ifBit 0 (.x a), .free t]).depth == 2
#guard (Circuit.mk 2 [.alloc t, .measure t 0, .ifBit 0 (.x a), .ifBit 0 (.x b), .free t]).layers
  == #[[.measure t 0], [.ifBit 0 (.x a), .ifBit 0 (.x b)]]
#guard (Circuit.mk 3 [.alloc t, .alloc (.anc 1), .free t, .free (.anc 1)]).peakAncilla == 2
#guard (Circuit.mk 3 [.alloc t, .free t, .alloc (.anc 1), .free (.anc 1)]).grade == ⟨4, 0, 0, 1⟩

/-! ## Decision 1 — `toNetwork`: AND count = ĉ∧ of ℰ on the corpus -/

def groverSrc : String := include_str "../../examples/grover_pred_037.cqr"
def orSrc : String := include_str "../../examples/search_or.cqr"
def chainSrc : String := include_str "../../examples/and_chain_8.cqr"
def whileSrc : String := include_str "../../examples/search_while.cqr"
def treeSrc : String := include_str "../../examples/allocate_tree.cqr"

/-- Constructs ℰ counts specially: `for` (unrolled), `if` (mux, one AND per bit), calls,
`xor`, `let`, a `Nat` loop index used as a value. -/
def forSrc : String :=
  "fn f(x: Vec Bool 4) -> Bool { for i in [0 ..< 4] with acc = false do acc or idx(x, i) }"
def ifSrc : String :=
  "fn f(x: Vec Bool 3) -> Bool { if idx(x, 0) then idx(x, 1) else idx(x, 2) }"
def callSrc : String :=
  "fn g(a: Bool, b: Bool) -> Bool { a and b }\n\
   fn f(x: Vec Bool 4) -> Bool { g(idx(x, 0), idx(x, 1)) xor g(idx(x, 2), not idx(x, 3)) }"
def vecIfSrc : String :=
  "fn f(c: Bool, x: Vec Bool 3, y: Vec Bool 3) -> Vec Bool 3 { if c then x else y }"
def letSrc : String :=
  "fn f(x: Vec Bool 3) -> Bool { let u = idx(x, 0) and idx(x, 1) in u or (u and idx(x, 2)) }"
def natSrc : String :=
  "fn f(n: Nat 4) -> Nat 4 { for i in [0 ..< 4] with acc = n do i }"

/-- Front end. -/
def typed (src : String) : Except Diagnostic TypedProgram := parse src >>= check
/-- ĉ∧ from ℰ. -/
def cAnd (src : String) : Option Nat := ((typed src).map (extract · |>.andComplexity)).toOption
/-- AND nodes of `toNetwork`. -/
def netAnds (src : String) : Option Nat := ((typed src >>= toNetwork).map (·.andCount)).toOption

#guard [groverSrc, orSrc, chainSrc, forSrc, ifSrc, callSrc, vecIfSrc, letSrc].all fun s =>
  (cAnd s).isSome && cAnd s == netAnds s
#guard [groverSrc, orSrc, chainSrc, forSrc, ifSrc, callSrc, vecIfSrc, letSrc].map cAnd ==
  [some 2, some 1, some 8, some 4, some 1, some 2, some 3, some 3]
-- `loop … while` has no finite network; `allocate_tree` already fails the surface checker.
#guard match typed whileSrc >>= toNetwork with
  | .error d => d.stage == .synthesis && d.code == .unboundedLoop
  | .ok _ => false
#guard (typed treeSrc).toOption.isNone
-- The `Nat 4` result of `natSrc` is the constant 3 (last index), little-endian.
#guard ((typed natSrc >>= toNetwork).map fun N => N.eval (fun _ => false)).toOption ==
  some [true, true]

/-- The network's output on the input bits of `k` (bit `i` of `k` = input `i`). -/
def evalAt (src : String) (k : Nat) : Option (List Bool) :=
  ((typed src >>= toNetwork).map (·.eval (fun i => (k >>> i) % 2 == 1))).toOption

-- Truth tables against the source semantics.
#guard (List.range 256).all fun k =>
  evalAt groverSrc k == some [(k % 2 == 1) && ((k >>> 3) % 2 == 1) && ((k >>> 7) % 2 == 1)]
#guard (List.range 16).all fun k => evalAt orSrc k == some [k % 4 != 0]
#guard (List.range 16).all fun k => evalAt forSrc k == some [k != 0]
#guard (List.range 8).all fun k =>
  evalAt ifSrc k == some [if k % 2 == 1 then (k >>> 1) % 2 == 1 else (k >>> 2) % 2 == 1]
#guard (List.range 16).all fun k =>
  evalAt callSrc k == some [(k % 4 == 3) ^^ ((k >>> 2) % 4 == 1)]

/-! ## Decision 2 — the straight-line oracle; §6.1.4, Table 3 -/

/-- Front end + network + oracle. -/
def oracle (src : String) : Except Diagnostic Circuit :=
  typed src >>= toNetwork >>= synthesizeOracle

-- Table 3 claims (w, d, t, a) = (10, 21, 8, 2). Measured with the decision-4 scheduler:
-- w = 10, t = 8, a = 2 hold; d = 27 (compute 11 + 9 overlapping, Z 1, MBU 3 + 3).
#guard ((oracle groverSrc).map grade).toOption == some ⟨10, 27, 8, 2⟩
#guard ((oracle groverSrc).map (·.validate.isOk)).toOption == some true
-- §6.1.4 listing: AND(x0, x3) → anc0, AND(anc0, x7) → anc1, Z anc1, MBU anc1, MBU anc0.
#guard ((oracle groverSrc).map (·.gates)).toOption == some
  ([.alloc (.anc 0)] ++ TempLogicalAND (.data 0) (.data 3) (.anc 0) ++
   [.alloc (.anc 1)] ++ TempLogicalAND (.anc 0) (.data 7) (.anc 1) ++
   [.z (.anc 1)] ++
   UncomputeTempLogicalAND (.anc 0) (.data 7) (.anc 1) 0 ++ [.free (.anc 1)] ++
   UncomputeTempLogicalAND (.data 0) (.data 3) (.anc 0) 1 ++ [.free (.anc 0)])
/-- Eq. 2 / Eq. 5 measured: `(t, a, w − n, ĉ∧)`, and the circuit is well formed. -/
def eq2 (s : String) : Option (Nat × Nat × Nat × Nat) :=
  match oracle s, cAnd s, typed s with
  | .ok c, some k, .ok tp =>
    let n := (tp.params.map (·.2.width)).sum
    if c.validate.isOk then some (c.grade.t, c.grade.a, c.grade.w - n, k)
    else none
  | _, _, _ => none

-- t = 4ĉ∧, a = w − n = ĉ∧ when every AND is in the cone and none folds.
#guard [groverSrc, orSrc, chainSrc, ifSrc, callSrc, letSrc].all fun s =>
  match eq2 s with
  | some (t, a, w, k) => t == 4 * k && a == k && w == k
  | none => false
-- `forSrc` starts the fold at `false`: the first `or` is `¬(¬0 ∧ ¬x0) = x0`, folded.
#guard eq2 forSrc == some (12, 3, 3, 4)
-- Folded identities: x ∧ x = x; x ∧ ¬x = 0 (constant: global phase, no gate);
-- (x0 ⊕ x1) ∧ (x1 ⊕ x0) = x0 ⊕ x1 (Z on a gathered qubit).
#guard ((oracle "fn f(x: Vec Bool 2) -> Bool { idx(x, 0) and idx(x, 0) }").map
  (·.gates)).toOption == some [.z (.data 0)]
#guard ((oracle "fn f(x: Vec Bool 2) -> Bool { idx(x, 0) and not idx(x, 0) }").map
  (·.gates)).toOption == some []
#guard ((oracle
  "fn f(x: Vec Bool 2) -> Bool { (idx(x, 0) xor idx(x, 1)) and (idx(x, 1) xor idx(x, 0)) }").map
  (·.gates)).toOption == some [.cnot (.data 1) (.data 0), .z (.data 0), .cnot (.data 1) (.data 0)]
-- ĉ∧ = 0: Z on the data qubit (X-sandwiched for a negative literal).
#guard ((oracle "fn f(x: Vec Bool 2) -> Bool { idx(x, 1) }").map (·.gates)).toOption ==
  some [.z (.data 1)]
#guard ((oracle "fn f(x: Vec Bool 2) -> Bool { not idx(x, 1) }").map (·.gates)).toOption ==
  some [.x (.data 1), .z (.data 1), .x (.data 1)]
-- Rejection: a multi-bit result has no phase oracle.
#guard match oracle vecIfSrc with
  | .error d => d.stage == .synthesis && d.code == .unsupportedNetwork
  | .ok _ => false

/-! ## Decision 3 — Bennett pebbling of a chain; §6.1.3, Table 2 (c∧ = 8) -/

/-- A Table 2 row as measured: `(feasible, rounds, depth, executed T)`. -/
def row (aMax : Nat) : Bool × Nat × Nat × Nat :=
  match pebbleChain 8 aMax with
  | .ok ms =>
    let c := Bennett.chainCircuit 9 (List.range 9) ms
    (true, Bennett.rounds ms, c.depth, c.tCount)
  | .error _ => (false, 0, 0, 0)

-- `pebbleChain 8 8`: 1 round, T = 32 (the straight-line schedule).
#guard ((pebbleChain 8 8).map fun ms => (Bennett.rounds ms, 4 * Bennett.placements ms)).toOption
  == some (1, 32)
#guard row 8 == (true, 1, 99, 32)
-- a_max = 4: feasible, 2 rounds, 12 forward placements, T = 48 ≤ 32 × 2 (Table 2: ×2, ≤ 64);
-- measured depth multiplier 144 / 99 ≈ 1.45.
#guard row 4 == (true, 2, 144, 48)
#guard (row 4).2.2.2 ≤ 32 * 2
-- a_max = 2 and 1: infeasible under decision 3 (with p pebbles node 2^p − 1 is the farthest
-- reachable; Table 2 lists ×8 and ×128 — report erratum, DECISIONS.md).
#guard (row 2).1 == false && (row 1).1 == false && (row 3).1 == false
-- Schedules are valid circuits with peak ancilla ≤ a_max; the full one has the oracle's grade.
#guard [8, 4].all fun k => match pebbleChain 8 k with
  | .ok ms => let c := Bennett.chainCircuit 9 (List.range 9) ms
              c.validate.isOk && c.peakAncilla ≤ k
  | .error _ => false
#guard ((pebbleChain 8 8).map (grade <| Bennett.chainCircuit 9 (List.range 9) ·)).toOption ==
  ((oracle chainSrc).map grade).toOption
-- The Grover predicate is a chain over (x0, x3, x7).
#guard ((typed groverSrc >>= toNetwork).map Bennett.chainOf).toOption == some (some [0, 3, 7])
#guard ((typed orSrc >>= toNetwork).map Bennett.chainOf).toOption == some none

end CQRV.Tests.Synthesis
