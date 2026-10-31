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

/-! ## Stage 15a — coherent uncomputation (PHASE2_SPEC.md §A.0.1) -/

-- The adjoint of the §6.2.2 compute listing, gate for gate (13 gates, 4 T).
#guard adjointGates (TempLogicalAND a b t) ==
  [.sdg t, .h t, .cnot t b, .cnot t a, .tdg t, .t b, .t a, .cnot t b, .cnot t a, .cnot b t,
   .cnot a t, .tdg t, .h t]
#guard UncomputeTempLogicalANDCoherent a b t == adjointGates (TempLogicalAND a b t)
#guard (UncomputeTempLogicalANDCoherent a b t).foldl (· + ·.tCount) 0 == 4
/-- A gate of the unitary fragment (`Gate.isUnitary` of `CQRV.Circuit.Semantics`, restated here:
the test imports the synthesizer only). -/
def unitaryGate : Gate → Bool
  | .measure _ _ | .ifBit _ _ => false
  | _ => true

#guard (UncomputeTempLogicalANDCoherent a b t).all unitaryGate
#guard adjointGates (adjointGates (TempLogicalAND a b t)) == TempLogicalAND a b t
#guard UncomputeMode.parse? "coherent" == some .coherent &&
  UncomputeMode.parse? "mbu" == some .mbu && UncomputeMode.parse? "x" == none

/-- Front end + network + oracle in mode `coherent`. -/
def oracleC (src : String) : Except Diagnostic Circuit :=
  typed src >>= toNetwork >>= (synthesizeOracle · .coherent)

/-- A circuit without `measure` and `ifBit`. -/
def measurementFree (c : Circuit) : Bool := c.gates.all unitaryGate

-- The running example in mode `coherent`: 8 T per AND (16), no classical bit, no measurement,
-- same width and ancillae as MBU, (10, 41, 16, 2) against (10, 27, 8, 2); the gate list is the
-- §6.1.4 listing with the adjoint blocks in place of the MBU blocks.
#guard ((oracleC groverSrc).map (·.tCount)).toOption == some 16
#guard ((oracleC groverSrc).map (·.nBits)).toOption == some 0
#guard ((oracleC groverSrc).map measurementFree).toOption == some true
#guard ((oracleC groverSrc).map (·.validate.isOk)).toOption == some true
#guard ((oracleC groverSrc).map grade).toOption == some ⟨10, 41, 16, 2⟩
#guard ((oracleC groverSrc).map (·.gates)).toOption == some
  ([.alloc (.anc 0)] ++ TempLogicalAND (.data 0) (.data 3) (.anc 0) ++
   [.alloc (.anc 1)] ++ TempLogicalAND (.anc 0) (.data 7) (.anc 1) ++
   [.z (.anc 1)] ++
   UncomputeTempLogicalANDCoherent (.anc 0) (.data 7) (.anc 1) ++ [.free (.anc 1)] ++
   UncomputeTempLogicalANDCoherent (.data 0) (.data 3) (.anc 0) ++ [.free (.anc 0)])
-- Mode `mbu` is the Phase 1 synthesizer gate for gate (the default argument), on the corpus.
#guard [groverSrc, orSrc, chainSrc, ifSrc, callSrc, letSrc, forSrc].all fun s =>
  (typed s >>= toNetwork >>= synthesizeOracle).toOption ==
    (typed s >>= toNetwork >>= (synthesizeOracle · .mbu)).toOption
-- In mode `coherent` every corpus oracle is measurement-free, bit-free, valid, with twice the T
-- count and the same width and ancillae as in mode `mbu`.
#guard [groverSrc, orSrc, chainSrc, ifSrc, callSrc, letSrc, forSrc].all fun s =>
  match oracle s, oracleC s with
  | .ok m, .ok c => measurementFree c && c.nBits == 0 && c.validate.isOk &&
      c.tCount == 2 * m.tCount && c.grade.w == m.grade.w && c.grade.a == m.grade.a
  | _, _ => false
-- The tree diffusion D₈ in both modes: (15, 41, 28, 7) MBU, (15, 59, 56, 7) coherent.
#guard ((diffusion 8 none).map grade).toOption == some ⟨15, 41, 28, 7⟩
#guard ((diffusion 8 none .tree .coherent).map grade).toOption == some ⟨15, 59, 56, 7⟩
#guard ((diffusion 8 none .tree .coherent).map (·.validate.isOk)).toOption == some true
#guard ((diffusion 8 none .tree .coherent).map measurementFree).toOption == some true
-- The Grover circuit of the running example, r = 2: (15, 134, 72, 7) MBU, (15, 200, 144, 7)
-- coherent (no classical bit).
#guard ((typed groverSrc >>= toNetwork >>= (groverCircuit · 8 2 none .tree .coherent)).map
  grade).toOption == some ⟨15, 200, 144, 7⟩
#guard ((typed groverSrc >>= toNetwork >>= (groverCircuit · 8 2 none .tree .coherent)).map
  (·.nBits)).toOption == some 0
#guard ((typed groverSrc >>= toNetwork >>= (groverCircuit · 8 2)).map grade).toOption ==
  some ⟨15, 134, 72, 7⟩
-- Bennett pebbling is MBU-only: a budget below the straight-line count with mode `coherent` is
-- `unsupported_combination`; a budget that covers it is the straight-line coherent oracle.
#guard match synthesizeWithBudget (allNet 8) (some 3) .coherent with
  | .error d => d.stage == .synthesis && d.code == .unsupportedCombination
  | .ok _ => false
#guard ((synthesizeWithBudget (allNet 8) (some 7) .coherent).map (·.1)).toOption ==
  some "straight-line"
#guard ((synthesizeWithBudget (allNet 8) (some 3)).map (·.1)).toOption == some "bennett(amax=3)"

/-! ## Stage 9a review — `Network.WF` on the corpus -/

def xorPredSrc : String := include_str "../../tests/certify/xor_pred.cqr"
def ifPredSrc : String := include_str "../../tests/certify/if_pred.cqr"

/-- `toNetwork` of a source; `none` when the front end rejects it or there is no network. -/
def netOf (src : String) : Option Network := (parse src >>= check >>= toNetwork).toOption

-- Every corpus file with a network (examples/, tests/certify/, the inline programs above)
-- gives a well-formed network; search_while (unbounded loop) and allocate_tree (rejected by the
-- checker) have none.
#guard [groverSrc, orSrc, chainSrc, xorPredSrc, ifPredSrc, forSrc, ifSrc, callSrc, vecIfSrc,
    letSrc].all fun src => (netOf src).any (·.wf)
#guard (netOf whileSrc).isNone && (netOf treeSrc).isNone
-- Each clause of `Network.wf` rejects: an input outside `nInputs` (the synthesizer would emit
-- `Z x[5]`), a forward operand, an output outside the nodes.
#guard !(Network.mk 0 #[.input 5] [0]).wf
#guard !(Network.mk 2 #[.input 0, .input 1, .and 0 3, .xor 0 1] [2]).wf
#guard !(Network.mk 1 #[.input 0] [1]).wf
#guard (Network.mk 2 #[.input 0, .input 1, .and 0 1] [2]).wf
example : (Network.mk 2 #[.input 0, .input 1, .xor 0 1, .not 2] [3]).WF := by decide

/-! ## Stage 17a — `GradeExt` from the decision-4 schedule (PHASE2_SPEC.md §A.1) -/

/-- Hand-built. Layers: L1 `H x0` and `measure anc0`; L2 `T x0`; L3 `CNOT`; L4 `T x1`, `T† x0`;
L5 `if c0: CZ`; L6 `P(1/16) x0`; L7 `CP(1/4)`; L8 `CP(1/2)`. Two-qubit gates: CNOT, CZ (under
`ifBit`), two CP = 4; T-layers L2 and L4 = 2; rotations `P(1/16)`, `CP(1/4)` = 2 (`CP(1/2)` is
Clifford); one measurement; one `ifBit`. Grade (3, 8, 3, 1). -/
def extC : Circuit := ⟨2, [.alloc t, .h a, .t a, .cnot a b, .t b, .tdg a, .measure t 0,
  .ifBit 0 (.cz a b), .p 1 4 a, .cp 1 2 a b, .cp 1 1 a b, .free t]⟩

#guard extC.validate.isOk
#guard extC.gradeExt == ⟨4, 2, 2, 1, 1⟩ && extC.grade == ⟨3, 8, 3, 1⟩
#guard extC.layerDump == "L1: H x[0]; measure anc[0] → c0\nL2: T x[0]\nL3: CNOT x[0] x[1]\n\
  L4: T x[1]; T† x[0]\nL5: if c0: CZ x[0] x[1]\nL6: P(1/16) x[0]\nL7: CP(1/4) x[0] x[1]\n\
  L8: CP(1/2) x[0] x[1]"
-- `TempLogicalAND` alone (§6.2.2 listing): 6 CNOT, T-depth 3 (its 4 T / T† sit in 3 layers), no
-- measurement; with its MBU uncompute: the `if c0: CZ` is a seventh two-qubit gate, one
-- measurement, two `ifBit`.
#guard andOnly.gradeExt == ⟨6, 3, 0, 0, 0⟩
#guard andPair.gradeExt == ⟨7, 3, 0, 1, 2⟩
-- The running example (`grover_pred_037`, n = 8, r = 2), measured: MBU (15, 134, 72, 7) with
-- 126 two-qubit gates, T-depth 39, no rotation, 18 measurements, 36 `ifBit`; coherent
-- (15, 200, 144, 7) with 216, 74, 0, 0, 0; the oracle alone (10, 27, 8, 2) with 14, 5, 0, 2, 4.
#guard ((typed groverSrc >>= toNetwork >>= (groverCircuit · 8 2)).map Circuit.gradeExt).toOption
  == some ⟨126, 39, 0, 18, 36⟩
#guard ((typed groverSrc >>= toNetwork >>= (groverCircuit · 8 2 none .tree .coherent)).map
  Circuit.gradeExt).toOption == some ⟨216, 74, 0, 0, 0⟩
#guard ((oracle groverSrc).map Circuit.gradeExt).toOption == some ⟨14, 5, 0, 2, 4⟩
-- D₈ (tree): MBU 49, 7, 0, 7, 14; coherent 84, 22, 0, 0, 0. `mczFew 8 .logDepth` (10, 58, 40, 2):
-- 39, 33, 0, 2, 4.
#guard ((diffusion 8 none).map Circuit.gradeExt).toOption == some ⟨49, 7, 0, 7, 14⟩
#guard ((diffusion 8 none .tree .coherent).map Circuit.gradeExt).toOption == some ⟨84, 22, 0, 0, 0⟩
#guard ((CQRV.Synthesis.mczFew 8 .logDepth).map fun c => (c.gradeExt, c.grade)).toOption ==
  some (⟨39, 33, 0, 2, 4⟩, ⟨10, 58, 40, 2⟩)
-- `Synthesis.gradeExt` is `Circuit.gradeExt`; `meas = nBits`; `tDepth ≤ depth`, `tDepth ≤ tCount`.
#guard ((typed groverSrc >>= toNetwork >>= (groverCircuit · 8 2)).map fun c =>
  Synthesis.gradeExt c == c.gradeExt && c.gradeExt.meas == c.nBits &&
  c.gradeExt.tDepth ≤ c.depth && c.gradeExt.tDepth ≤ c.tCount).toOption == some true
example : extC.gradeExt.meas = extC.nBits := Circuit.gradeExt_meas_eq_nBits extC
example : extC.gradeExt.tDepth ≤ extC.depth := Circuit.gradeExt_tDepth_le_depth extC
example : extC.gradeExt.tDepth ≤ extC.tCount := Circuit.gradeExt_tDepth_le_tCount extC
-- Stage 17a invariant: no synthesized circuit contains a phase gate (`rot = 0` everywhere).
#guard [groverSrc, orSrc, chainSrc, ifSrc, callSrc, letSrc, forSrc].all fun s =>
  match oracle s, oracleC s with
  | .ok m, .ok c => m.gradeExt.rot == 0 && c.gradeExt.rot == 0 &&
      (m.gates ++ c.gates).all fun g => match g with | .p .. | .cp .. => false | _ => true
  | _, _ => false

end CQRV.Tests.Synthesis
