module

public import CQRV.Certify.Generate
public import CQRV.Certify.RunReport
public import CQRV.Certify.Count
public import CQRV.Synthesis.Counting

/-!
# CQRV.Certify.CountCert

PHASE2_SPEC.md §A.4 "Amendments before Stage 20b3" (1)–(6), §A.5; docs/tasks/STAGE20B_TASK.md
20b3 C2; report §5.1.3, §8.4.1, §8.4.4 — **the counting certificate**: its own request record,
renderer, JSON record and run report, Physlib-free, called by `cqr certify --problem count
--precision m` (Stage 21a3, through the dispatch `CQRV.Patterns.instantiate`; Stage 20b3 called it
from `CertifyTool count-certify`, removed). Stage 21a3 (PHASE2_SPEC.md §A.5 amendment (5) and the
refinement (5′)): the solution count is `Option Nat` — decided by the kernel (`hM_count`,
`cert_count`) when `n ≤ --count-limit`, otherwise not decided (`cert` only; the JSON's ε is the
maximum over `a`, π/2^m + π²/4^m) — and the uncomputation mode is a field of the request. The Grover
pipeline (`groverInstance`, `CertRequest`, `renderCert*`, `Certificate`, `schemaVersion`) is not
touched; the literal printers, `predicateHash`, `circuitHash`, `proofHash`, `RefConfig`,
`gateCounts` and `CertRequest.progBlock` are reused unchanged.

The generated `Cert.lean` (namespace `CQRV.Cert.«<name>_count»`) is in the **compositional form**
of amendment (2): no flat literal of the circuit, but

* `net`, `prog`, `prog_scoped`, `net_ok`, `front_end` as the Grover certificates;
* the distinct blocks `h_layer`, `cg_0 … cg_{m−1}`, `inverse` as literals, each with its link to
  the builder (`_ok`), its measured `grade_eq` / `gradeExt_eq` and its `liveEnd` by
  `decide +kernel` (the Stage 19b probe form);
* `emitted := assembleCounting h_layer [cg_0, …] inverse` (a library definition) and `emitted_ok`
  by the library theorem `countingCircuit_of_blocks` and the block links — no kernel evaluation of
  the whole circuit;
* `grade_le`, the composed grade bound (`grade_assembleCounting_le`, the blocks' `grade_eq`,
  the arithmetic by `decide`), and `gradeExt_bound` (`gradeExt_assembleCounting`);
* `cert`, universal in `M` (amendment (3)): for every solution count `M ≥ 1` of the predicate,
  `ae_parametric_lemma_mk` at `n`, `M`, `net.pred n` (the field form of `ae_parametric_lemma`,
  whose record form makes the elaborator unfold `Network.pred` at every unification of `gp.P`);
  `hM_count` (the kernel-decided
  count) and `cert_count`, the instance at that count;
* `#print axioms cert` and `#print axioms cert_count`.

`ε` and `δ` are reals (amendment (4)): the JSON gives each as an expression string and a decimal
marked approximate, never as a rational. The schema is 1.10.0 with `pattern "Count"`
(amendment (5)). Only the exact inverse QFT (`kmax = none`) is rendered (amendment (6)).
-/

@[expose] public section

namespace CQRV.Certify

open CQRV CQRV.Synthesis Lean

/-! ## The blocks -/

/-- One distinct block of the counting circuit: its name in `Cert.lean`, the circuit, the number
of copies in program order, and the phase qubit of a controlled iterate (`none` for the Hadamard
layer and the inverse block). -/
structure CountBlock where
  name : String
  circuit : Circuit
  mult : Nat
  phase : Option Nat
  deriving Repr, Inhabited

/-- PHASE2_SPEC.md §A.3 amendment (4), §A.4 (amendments before Stage 20b3, (2)) — the distinct
blocks of `countingCircuit N n m kmax shape mode` in program order: the Hadamard layer, the `m`
controlled iterates (block `j` with multiplicity `2^j`), the inverse (A)QFT. -/
def countBlocks (N : Network) (n m : Nat) (kmax : Option Nat) (shape : DiffusionShape)
    (mode : UncomputeMode) : Except DSL.Diagnostic (List CountBlock) := do
  let cgs ← (List.range m).mapM fun j => controlledGrover N n m j shape mode
  return [⟨"h_layer", countingHLayer n m, 1, none⟩] ++
    (cgs.zipIdx.map fun (b, j) => ⟨s!"cg_{j}", b, 2 ^ j, some j⟩) ++
    [⟨"inverse", countingInverse n m kmax, 1, none⟩]

/-- The controlled iterates among the blocks, in order. -/
def iterateBlocks (bs : List CountBlock) : List CountBlock := bs.filter (·.phase.isSome)

/-- Report §3.1.4, Stage 19a — the composed grade bound `init ⊕ ∑ mult • block ⊕ inv`, the value
of the right-hand side of `grade_assembleCounting_le`. -/
def composedGrade : List CountBlock → Grade
  | [] => 0
  | b :: rest => rest.foldl (fun g c => g + c.mult • Synthesis.grade c.circuit)
      (Synthesis.grade b.circuit)

/-- PHASE2_SPEC.md §A.3 amendment (6) — the composed second record: the sums, and the T-depth
bound `tDepth(init) + ∑ mult · tCount` (the right-hand sides of `gradeExt_assembleCounting`). -/
def composedGradeExt : List CountBlock → GradeExt
  | [] => ⟨0, 0, 0, 0, 0⟩
  | b :: rest => rest.foldl (fun g c =>
      let e := Synthesis.gradeExt c.circuit
      ⟨g.twoQ + c.mult * e.twoQ, g.tDepth + c.mult * c.circuit.tCount, g.rot + c.mult * e.rot,
       g.meas + c.mult * e.meas, g.ff + c.mult * e.ff⟩) (Synthesis.gradeExt b.circuit)

/-! ## The request -/

/-- PHASE2_SPEC.md §A.4 (amendments before Stage 20b3, (1)) — what the counting certificate
specializes: the request's name and typed term, its network, the instance `(n, M, m)`
(`M` the kernel-decided count, `kmax = none`), the distinct blocks and the assembled circuit. -/
structure CountRequest where
  name : String
  net : Network
  prog : DSL.TypedProgram
  n : Nat
  m : Nat
  /-- the solution count, decided by the kernel in `Cert.lean` (`hM_count`, `cert_count`) when
  `n ≤ --count-limit`; `none` when not decided (amendment (5′): `cert` only) -/
  M : Option Nat
  /-- amendment (6): only the exact inverse QFT is certified -/
  kmax : Option Nat := none
  /-- Stage 21a3: the uncomputation mode of the blocks (`--uncompute mbu|coherent`) -/
  mode : UncomputeMode := .mbu
  blocks : List CountBlock
  /-- `assembleCounting h_layer [cg_0, …] inverse`: the circuit the QIR / QASM and the hash are
  of -/
  circuit : Circuit
  predicateHash : String

/-- The request of a typed program `tp` (network `net`, arity `n`) at precision `m`, shape tree,
mode `mode`, exact inverse QFT: the blocks, the assembled circuit (checked against
`countingCircuit` by compiled evaluation), and `M = Network.countSat net n` when `decideCount`
(Stage 21a3: `0 < --count-limit ∧ n ≤ --count-limit`), `none` otherwise. -/
def CountRequest.ofProgram (tp : DSL.TypedProgram) (src : String) (net : Network) (n m : Nat)
    (mode : UncomputeMode := .mbu) (decideCount : Bool := true) : Except String CountRequest := do
  if m == 0 then throw "the counting circuit needs at least one phase qubit (m ≥ 1)"
  let blocks ← (countBlocks net n m none .tree mode).mapError (·.message)
  let some hl := blocks.head? | throw "no blocks"
  let some inv := blocks.getLast? | throw "no blocks"
  let circuit := assembleCounting hl.circuit ((iterateBlocks blocks).map (·.circuit)) inv.circuit
  let C ← (countingCircuit net n m none .tree mode).mapError (·.message)
  if C != circuit then throw "assembleCounting of the blocks differs from countingCircuit"
  return { name := tp.name, net, prog := tp, n, m, M := if decideCount then some (net.countSat n) else none,
           mode, blocks, circuit, predicateHash := Certify.predicateHash src }

/-- The Lean literal of the request's mode (`.mbu` / `.coherent`), as `Cert.lean` writes it. -/
def CountRequest.modeLit (q : CountRequest) : String := s!".{q.mode}"


/-- The namespace of the generated declarations. -/
def CountRequest.namespace (q : CountRequest) : String := s!"CQRV.Cert.«{q.name}_count»"

/-- The fully qualified name of the universal theorem `cert` (as `#print axioms` prints it). -/
def CountRequest.theoremName (q : CountRequest) : String := s!"CQRV.Cert.{q.name}_count.cert"

/-- The fully qualified name of the instance theorem `cert_count`. -/
def CountRequest.countTheoremName (q : CountRequest) : String :=
  s!"CQRV.Cert.{q.name}_count.cert_count"

/-- The composed grade bound of the request. -/
def CountRequest.grade (q : CountRequest) : Grade := composedGrade q.blocks

/-- The composed second record of the request (`tDepth` a bound). -/
def CountRequest.gradeExt (q : CountRequest) : GradeExt := composedGradeExt q.blocks

/-- The `CertRequest` stub that `CertRequest.progBlock` renders the front-end block from (the
`front-end` probe of Stage 18a does the same; only `name`, `net`, `prog`, `n` are read). -/
def CountRequest.frontEndStub (q : CountRequest) : CertRequest :=
  { name := q.name, net := q.net, prog := q.prog, n := q.n, M := 0, r := 0,
    circuit := ⟨q.n, []⟩, delta := 0, grade := ⟨0, 0, 0, 0⟩, gradeExt := ⟨0, 0, 0, 0, 0⟩,
    nAnc := 0, predicateHash := "" }

/-! ## ε and δ as reals (amendment (4)) -/

/-- `π` as a `Float`. -/
def piFloat : Float := Float.acos (-1)

/-- A `Float` rounded to six decimals (the `approx` of the JSON). -/
def round6 (x : Float) : Float := (Float.round (x * 1000000)) / 1000000

/-- PHASE2_SPEC.md §A.4 — `ae_eps a m = 2π√(a(1−a))/2^m + π²/4^m` as a `Float`, `a = M/2^n`. -/
def aeEpsFloat (n M m : Nat) : Float :=
  let a : Float := M.toFloat / (2 ^ n : Nat).toFloat
  2 * piFloat * (a * (1 - a)).sqrt / (2 ^ m : Nat).toFloat +
    piFloat * piFloat / (4 ^ m : Nat).toFloat

/-- PHASE2_SPEC.md §A.4 — `ae_delta = 1 − 8/π²` as a `Float`. -/
def aeDeltaFloat : Float := 1 - 8 / (piFloat * piFloat)

/-- The expression string of `ε` at the instance. -/
def aeEpsExpr (n M m : Nat) : String :=
  s!"2*pi*sqrt(a*(1-a))/2^{m} + pi^2/4^{m} with a = M/2^n = {M}/{2 ^ n}"

/-- The expression string of `δ`. -/
def aeDeltaExpr : String := "1 - 8/pi^2"

/-- PHASE2_SPEC.md §A.5 (5′) — the maximum over `a ∈ [0, 1]` of `ae_eps a m`: `π/2^m + π²/4^m`
(`2π√(a(1−a)) ≤ π`), the ε stated when the solution count is not decided. -/
def aeEpsMaxFloat (m : Nat) : Float :=
  piFloat / (2 ^ m : Nat).toFloat + piFloat * piFloat / (4 ^ m : Nat).toFloat

/-- The expression string of the maximum (5′). -/
def aeEpsMaxExpr (m : Nat) : String :=
  s!"max over a in [0,1] of 2*pi*sqrt(a*(1-a))/2^{m} + pi^2/4^{m} = pi/2^{m} + pi^2/4^{m}"

/-- The ε of a request as `(expr, approx)`: at the decided count, or its maximum over `a` (5′). -/
def CountRequest.eps (q : CountRequest) : String × Float :=
  match q.M with
  | some M => (aeEpsExpr q.n M q.m, aeEpsFloat q.n M q.m)
  | none => (aeEpsMaxExpr q.m, aeEpsMaxFloat q.m)

/-- Amendment (4) — the half-width of the guarantee in units of `M`: `ε · 2^n`, rounded to the
nearest integer ("about ±43" at `n = 8`, `M = 32`, `m = 4`: `0.1684 · 256 = 43.1`). -/
def mUnits (n M m : Nat) : Nat := (aeEpsFloat n M m * (2 ^ n : Nat).toFloat).round.toUInt64.toNat

/-! ## The text of `Cert.lean` -/

/-- A grade as a Lean anonymous-constructor literal. -/
def gradeLit (g : Grade) : String := s!"⟨{g.w}, {g.d}, {g.t}, {g.a}⟩"

/-- A `GradeExt` as a Lean anonymous-constructor literal. -/
def gradeExtLit (e : GradeExt) : String := s!"⟨{e.twoQ}, {e.tDepth}, {e.rot}, {e.meas}, {e.ff}⟩"

/-- The declarations of one block: the literal, the link to the builder, `grade_eq`,
`gradeExt_eq`, `liveEnd` (the Stage 19b probe form, with `_liveEnd` added). -/
def CountRequest.blockDecls (q : CountRequest) (b : CountBlock) : String :=
  let g := Synthesis.grade b.circuit
  let e := Synthesis.gradeExt b.circuit
  let link := match b.phase with
    | some j => s!"theorem {b.name}_ok : controlledGrover net {q.n} {q.m} {j} .tree {q.modeLit} = .ok {b.name} :=
  except_ok_of_check _ _ (by decide +kernel)"
    | none =>
      if b.name == "h_layer" then
        s!"theorem {b.name}_ok : countingHLayer {q.n} {q.m} = {b.name} := by decide +kernel"
      else s!"theorem {b.name}_ok : countingInverse {q.n} {q.m} none = {b.name} := by decide +kernel"
  s!"/-- Block `{b.name}`: {b.circuit.gates.length} gates, multiplicity {b.mult}, `liveEnd` {b.circuit.liveEnd}. -/
def {b.name} : Circuit := {circuitLit b.circuit}

/-- The link to the builder (as `emitted_ok` of a Grover certificate). -/
{link}

/-- The measured grade of `{b.name}` (as `grade_eq`). -/
theorem {b.name}_grade_eq : Synthesis.grade {b.name} = {gradeLit g} := by decide +kernel

/-- The measured `GradeExt` of `{b.name}` (as `gradeExt_eq`). -/
theorem {b.name}_gradeExt_eq : Synthesis.gradeExt {b.name} = {gradeExtLit e} := by decide +kernel

/-- `{b.name}` ends with no live ancilla (a hypothesis of the composed bound). -/
theorem {b.name}_liveEnd : {b.name}.liveEnd = 0 := by decide +kernel
"

/-- The Lean list of the controlled iterates, `[cg_0, cg_1, …]`. -/
def CountRequest.iterateList (q : CountRequest) : String :=
  "[" ++ ", ".intercalate ((iterateBlocks q.blocks).map (·.name)) ++ "]"

/-- The `rcases` pattern for a membership in the iterate list, `rfl | rfl | …`. -/
def CountRequest.rflPattern (q : CountRequest) : String :=
  " | ".intercalate ((iterateBlocks q.blocks).map fun _ => "rfl")

/-- The `exacts [cg_0_liveEnd, …]` closing the membership cases in order. -/
def CountRequest.liveEndAlts (q : CountRequest) : String :=
  "exacts [" ++ ", ".intercalate ((iterateBlocks q.blocks).map fun b => s!"{b.name}_liveEnd") ++ "]"

/-- The `match` on the phase qubit for `countingCircuit_of_blocks`. -/
def CountRequest.matchArms (q : CountRequest) : String :=
  String.join ((iterateBlocks q.blocks).map fun b =>
    s!"\n      | {b.phase.getD 0}, _ => {b.name}_ok") ++
    s!"\n      | _ + {q.m}, h => absurd h (by omega)"

/-- The simp lemmas that expand the sum over the iterate list and rewrite the blocks' records. -/
def CountRequest.simpSet (q : CountRequest) (suffix : String) (arith : String) : String :=
  "List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.sum_cons, \
    List.sum_nil, Nat.reducePow" ++ arith ++
    String.join (q.blocks.map fun b => s!", {b.name}_{suffix}")

/-- The header sentence on the solution count and ε: the decided count with `cert_count`, or the
not-decided case of (5′) with ε as the maximum over `a`. -/
def CountRequest.headerClaim (q : CountRequest) : String :=
  match q.M with
  | some M => s!"shape tree, uncompute = {q.mode}; `cert` is universal in the solution
count M ≥ 1 (no claim for M = 0), `cert_count` its instance at M = {M} (decided by the kernel:
`hM_count`). ε = {aeEpsExpr q.n M q.m} ≈ {round6 (aeEpsFloat q.n M q.m)}, δ = {aeDeltaExpr} ≈ {round6 aeDeltaFloat}."
  | none => s!"shape tree, uncompute = {q.mode}; `cert` is universal in the solution
count M ≥ 1 (no claim for M = 0); the solution count is not decided (n = {q.n} above
`--count-limit`), so there is no `cert_count`. ε ≤ {aeEpsMaxExpr q.m} ≈ {round6 (aeEpsMaxFloat q.m)}
(the maximum over a of ae_eps a {q.m}), δ = {aeDeltaExpr} ≈ {round6 aeDeltaFloat}."

/-- `hM_count` (the kernel-decided count) with its doc-comment, or nothing. -/
def CountRequest.hMCountDecl (q : CountRequest) : String :=
  match q.M with
  | some M => s!"/-- Report §8.2 (Stage 14a) — the solution count, decided by the kernel: `Network.countSat`
evaluates `net` on all 2^{q.n} inputs; `Network.countSat_eq_card` identifies that count with the
cardinality of the statement. -/
theorem hM_count : (Finset.univ.filter fun x => Network.pred net {q.n} x = true).card = {M} := by
  rw [← Network.countSat_eq_card]
  decide +kernel

"
  | none => ""

/-- `cert_count` (the instance at the kernel-decided count) with its audit line, or nothing. -/
def CountRequest.certCountDecl (q : CountRequest) : String :=
  match q.M with
  | some M =>
    let aCount := s!"(({M} : ℕ) / 2 ^ {q.n} : ℝ)"
    s!"/-- The instance at the kernel-decided count `M = {M}` (for the comparison with the Grover
certificate of the same predicate). -/
theorem cert_count :
    Realizes (CountSpec {q.m} {aCount}) (countPOVM {q.n} {q.m} {aCount}) (groverChannel {q.n + q.m} emitted)
        (ae_eps {aCount} {q.m}) ae_delta {gradeLit q.grade} ∧
      AncRestore {q.n + q.m} emitted.nAnc emitted (U_count (Network.pred net {q.n}) {q.m} none) :=
  cert {M} hM_count (by decide)

#print axioms cert_count

"
  | none => ""

/-- PHASE2_SPEC.md §A.4 (amendments before Stage 20b3, (2)–(4)), §A.5 (5), (5′); report §5.1.3,
§8.4.1, §8.4.4 — the text of `Cert.lean` (LF line endings) in the compositional form. With a
decided count it is the Stage 20b3 text (the header names `cqr certify --problem count` since
21m, PHASE2_SPEC §A.9 (6)); without one, `hM_count` and `cert_count` are absent. -/
def renderCountCert (q : CountRequest) : String :=
  let g := q.grade
  let e := q.gradeExt
  let n := q.n
  let m := q.m
  let aStr := s!"(M / 2 ^ {n} : ℝ)"
  s!"import CQRV

/-!
# Certificate `{q.name}_count` (generated by `cqr certify --problem count`; do not edit)

PHASE2_SPEC.md §A.4 (\"Amendments before Stage 20b3\" (1)–(6)), report §5.1.3, §8.4.1, §8.4.4: the
amplitude-estimation parametric lemma `ae_parametric_lemma` (Stage 20b1) specialized to the
counting circuit of the request in the compositional form — the distinct blocks as literals with
their links to the builder and their measured grades, the whole circuit as `assembleCounting` of
the blocks (`countingCircuit_of_blocks`), the composed grade bound (`grade_assembleCounting_le`) —
and checked by the Lean kernel (`lake env lean`). Instance: n = {n}, m = {m} (phase qubits),
kmax = none (exact inverse QFT), {q.headerClaim}
predicate_hash = {q.predicateHash}
-/

namespace {q.namespace}

open CQRV CQRV.Synthesis CQRV.Counting CQRV.Grover CQRV.Certify

/-- The Boolean network of the request (`toNetwork`, §6.1.2). -/
def net : Network := {networkLit q.net}

{q.frontEndStub.progBlock}
/-! ## The distinct blocks (PHASE2_SPEC.md §A.3 amendment (4); the Stage 19b probe form) -/

{String.join (q.blocks.map fun b => q.blockDecls b ++ "\n")}
/-! ## The assembled circuit -/

/-- The emitted circuit (IR, §6.1.4): the blocks assembled with their multiplicities
(`assembleCounting`); QIR / OpenQASM 3 and `circuit_hash` are of this circuit. -/
def emitted : Circuit := assembleCounting h_layer {q.iterateList} inverse

theorem emitted_def : emitted = assembleCounting h_layer {q.iterateList} inverse := rfl

/-- The hash link: `countingCircuit` on `net` is the assembled circuit, by the library theorem
`countingCircuit_of_blocks` and the block links (no kernel evaluation of the whole circuit). -/
theorem emitted_ok : countingCircuit net {n} {m} none .tree {q.modeLit} = .ok emitted := by
  have h := countingCircuit_of_blocks (N := net) (n := {n}) (m := {m}) none (shape := .tree)
    (mode := {q.modeLit}) (bs := {q.iterateList}) (by decide) rfl fun j hj =>
    match j, hj with{q.matchArms}
  rwa [h_layer_ok, inverse_ok, ← emitted_def] at h

/-- Every controlled iterate is on the data register of the Hadamard layer. -/
theorem blocks_nData : ∀ b ∈ {q.iterateList}, b.nData = h_layer.nData := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with {q.rflPattern} <;> rfl

/-- Every controlled iterate ends with no live ancilla. -/
theorem blocks_liveEnd : ∀ b ∈ {q.iterateList}, b.liveEnd = 0 := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with {q.rflPattern}
  {q.liveEndAlts}

/-- PHASE2_SPEC.md §A.4 (amendments before Stage 20b3, (2)), report §3.1.4 — the composed grade
bound: `grade_assembleCounting_le` with the blocks' `grade_eq`, the arithmetic by `decide`. -/
theorem grade_le : Synthesis.grade emitted ≤ {gradeLit g} := by
  have h := grade_assembleCounting_le h_layer {q.iterateList} inverse blocks_nData rfl
    h_layer_liveEnd blocks_liveEnd
  simp only [{q.simpSet "grade_eq" ""}] at h
  rw [emitted_def]
  exact le_trans h (by decide)

/-- PHASE2_SPEC.md §A.1, §A.3 amendment (6) — the composed second record: the sums are exact,
the T-depth is a bound (`gradeExt_assembleCounting`). -/
theorem gradeExt_bound :
    (Synthesis.gradeExt emitted).twoQ = {e.twoQ} ∧ (Synthesis.gradeExt emitted).rot = {e.rot} ∧
      (Synthesis.gradeExt emitted).meas = {e.meas} ∧ (Synthesis.gradeExt emitted).ff = {e.ff} ∧
      (Synthesis.gradeExt emitted).tDepth ≤ {e.tDepth} := by
  have h := gradeExt_assembleCounting h_layer {q.iterateList} inverse
  simp only [{q.simpSet "gradeExt_eq" ", Nat.reduceMul, Nat.reduceAdd"}{String.join ((iterateBlocks q.blocks ++ [q.blocks.getLast!]).map fun b => s!", {b.name}_grade_eq")}] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [emitted_def]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The network is well formed (a hypothesis of `ae_parametric_lemma`). -/
theorem hN : net.WF := by decide +kernel

{q.hMCountDecl}/-- PHASE2_SPEC.md §A.4 (amendments before Stage 20b3, (3)), report §2.1.2, §8.4.4 — **the
certificate, universal in the solution count**: for whatever the true count `M ≥ 1` of
`net.pred {n}` is, the Grover channel of the emitted counting circuit `(ae_eps (M/2^{n}) {m},
ae_delta)`-realizes `CountSpec {m} (M/2^{n})` under `countPOVM {n} {m} (M/2^{n})` within the composed
grade bound, and the circuit restores its ancillae while applying `U_count (net.pred {n}) {m} none`.
No claim is made for `M = 0`. -/
theorem cert : ∀ M : ℕ, (Finset.univ.filter fun x => Network.pred net {n} x = true).card = M →
    1 ≤ M →
    Realizes (CountSpec {m} {aStr}) (countPOVM {n} {m} {aStr}) (groverChannel {n + m} emitted)
        (ae_eps {aStr} {m}) ae_delta {gradeLit g} ∧
      AncRestore {n + m} emitted.nAnc emitted (U_count (Network.pred net {n}) {m} none) :=
  fun M hcard hpos =>
    ae_parametric_lemma_mk {n} M hpos (Network.pred net {n}) hcard (by decide) hN rfl rfl rfl
      emitted_ok _ grade_le

#print axioms cert

{q.certCountDecl}end {q.namespace}
"

/-! ## The JSON record (schema 1.10.0, amendment (5)) -/

/-- The schema version of a counting certificate (`pattern "Count"`): `Certify.schemaVersion`
("1.12.0" since revision R5; since Stage 21a3 every certificate says the same version,
PHASE2_SPEC.md §A.5 amendment (7)). -/
def countSchemaVersion : String := Certify.schemaVersion

/-- The `restoration` text of a counting certificate. -/
def countRestorationText (n m : Nat) : String :=
  s!"AncRestore: all ancillae |0…0⟩ on density operators, while applying U_count P {m} none on \
    Reg ({n} + {m})"

/-- The note of `hardware_perturbation` (the QASM measures every data qubit; the decoding POVM
reads the phase register only). -/
def countHardwareNote (n m : Nat) : String :=
  s!"the QASM / QIR measure all {n} + {m} = {n + m} data qubits; countPOVM reads the phase register \
    ({m} qubits) only, the search register being traced, which is the same POVM on the phase \
    outcomes; alloc/free not counted"

/-- The hypotheses listed in a counting certificate (amendment (3)–(4), (6); (5′) when the count
is not decided). -/
def countHypotheses (n m : Nat) (M : Option Nat) : List String :=
  [(match M with
    | some M => s!"solution_count M ≥ 1 (GroverData.hM_pos): `cert` is universal in M; no claim for M = 0; \
      `cert_count` is the instance at M = {M} (hM_count, decided by the kernel)"
    | none => s!"solution_count M ≥ 1 (GroverData.hM_pos): `cert` is universal in M; no claim for M = 0; \
      the count is not decided (n = {n} above --count-limit), so there is no `cert_count` and ε is \
      stated as its maximum over a = M/2^n (PHASE2_SPEC §A.5 (5′))"),
   s!"precision m = {m} phase qubits: ε = ae_eps (M/2^{n}) {m} and δ = ae_delta are stated at this m \
    (the precision grows with m)",
   "exact inverse QFT (kmax = none): the AQFT variant is the proved lemma ae_parametric_lemma_aqft, \
    not certified at this m (its bound is vacuous for m ≤ 6, PHASE2_SPEC §A.4 amendment (6))"]

/-- Report §8.4.2, §8.4.4, §9.5.3; PHASE2_SPEC.md §A.4 (amendments before Stage 20b3, (4)–(5)) —
the counting certificate record. -/
structure CountCertificate where
  name : String
  n : Nat
  /-- the kernel-decided count, or `none` when not decided (`instance.M` null, (5′)) -/
  M : Option Nat
  m : Nat
  kmax : Option Nat
  /-- ε and δ as reals: an expression and a decimal approximation -/
  epsExpr : String
  epsApprox : Float
  deltaExpr : String
  deltaApprox : Float
  /-- the composed grade bound (`grade_kind "composed_bound"`) -/
  grade : Grade
  /-- the composed second record (`t_depth` a bound) -/
  gradeExt : GradeExt
  blocks : List CountBlock
  hypotheses : List String
  restoration : String
  predicateHash : String
  circuitHash : String
  proofHash : Option String
  /-- R5: `hashes.library` (`Certify.libraryHash`), filled by `cqr certify` -/
  libraryHash : Option String := none
  gateCounts : GateCounts
  config : RefConfig
  axioms : List String
  status : Status
  theoremName : Option String
  obligations : List String
  frontEnd : String
  uncompute : UncomputeMode := .mbu

/-- The JSON of a block row (`blocks` of the schema). -/
def CountBlock.toJson (b : CountBlock) : Json :=
  let g := Synthesis.grade b.circuit
  let e := Synthesis.gradeExt b.circuit
  Json.mkObj [("name", Json.str b.name), ("gates", b.circuit.gates.length),
    ("multiplicity", b.mult),
    ("grade", Json.mkObj [("w", g.w), ("d", g.d), ("t", g.t), ("a", g.a)]),
    ("grade_ext", Json.mkObj [("two_qubit", e.twoQ), ("t_depth", e.tDepth), ("rot", e.rot),
      ("meas", e.meas), ("ff", e.ff)]),
    ("live_end", b.circuit.liveEnd)]

/-- Report §9.5.3; PHASE2_SPEC.md §A.4 (amendments before Stage 20b3, (5)) — the JSON envelope
of a counting certificate (`docs/certificate.schema.json`, the `Count` branch of 1.10.0). -/
def CountCertificate.toJson (c : CountCertificate) : Json :=
  let str (s : String) : Json := Json.str s
  let optStr : Option String → Json := fun | some s => str s | none => Json.null
  let real (expr : String) (approx : Float) : Json :=
    Json.mkObj [("expr", str expr), ("approx", Lean.toJson (round6 approx))]
  Json.mkObj
    [("schema_version", str countSchemaVersion),
     ("pattern", str "Count"),
     ("instance", Json.mkObj [("n", c.n),
       ("M", match c.M with | some M => Lean.toJson M | none => Json.null), ("m", c.m),
       ("kmax", match c.kmax with | some k => Lean.toJson k | none => Json.null)]),
     ("solution_count", Json.mkObj
       [("value", match c.M with | some M => Lean.toJson M | none => Json.null),
        ("status", str (if c.M.isSome then "kernel_decided" else "not_decided"))]),
     ("spec", Json.mkObj [("epsilon", real c.epsExpr c.epsApprox),
       ("delta", real c.deltaExpr c.deltaApprox), ("estimate", str "sin^2(pi*y/2^m)")]),
     ("grade", Json.mkObj [("w", c.grade.w), ("d", c.grade.d), ("t", c.grade.t),
       ("a", c.grade.a)]),
     ("grade_kind", str "composed_bound"),
     ("grade_ext", Json.mkObj [("two_qubit", c.gradeExt.twoQ), ("t_depth", c.gradeExt.tDepth),
       ("rot", c.gradeExt.rot), ("meas", c.gradeExt.meas), ("ff", c.gradeExt.ff),
       ("t_depth_kind", str "bound")]),
     ("blocks", Json.arr (c.blocks.map CountBlock.toJson).toArray),
     ("hypotheses", Json.arr (c.hypotheses.map str).toArray),
     ("restoration", str c.restoration),
     ("hashes", Json.mkObj [("predicate", str c.predicateHash), ("circuit", str c.circuitHash),
       ("proof", optStr c.proofHash), ("library", optStr c.libraryHash)]),
     ("trust_boundary", Json.mkObj [("emitted", str "QIR text"),
       ("profile", str "adaptive_profile"),
       ("emitter", str "unverified; translation-validated by re-parse"),
       ("front_end", str c.frontEnd)]),
     ("hardware_perturbation", Json.mkObj [("formula", str "δ_hw ≤ δ + G·p̄"),
       ("G", c.gateCounts.total), ("p_bar", str "profile parameter"),
       ("counts", Json.mkObj [("unitary", c.gateCounts.unitary),
         ("mid_circuit_measurements", c.gateCounts.midCircuitMeasurements),
         ("classically_controlled", c.gateCounts.classicallyControlled),
         ("terminal_measurements", c.gateCounts.terminalMeasurements)]),
       ("note", str (countHardwareNote c.n c.m)), ("status", str Certify.hardwarePerturbationStatus)]),
     ("reference_configuration", Json.mkObj [("lean", str c.config.lean),
       ("mathlib", str c.config.mathlib), ("physlib", str c.config.physlib),
       ("cpu", optStr c.config.cpu),
       ("logical_cpus", match c.config.logicalCpus with | some k => Lean.toJson k | none => Json.null),
       ("clock", optStr c.config.clock), ("lean_threads", optStr c.config.leanThreads),
       ("kernel_check", match c.config.kernelCheck with
         | some k => k.toJson
         | none => Json.null)]),
     ("theorem", optStr c.theoremName),
     ("axioms", Json.arr (c.axioms.map str).toArray),
     ("obligations", Json.arr (c.obligations.map str).toArray),
     ("status", str c.status.name),
     ("uncompute", str c.uncompute.toString)]

/-- The record of a request before the kernel check (status "not yet audited"). -/
def CountCertificate.ofRequest (q : CountRequest) (cfg : RefConfig) : CountCertificate :=
  { name := q.name, n := q.n, M := q.M, m := q.m, kmax := q.kmax,
    epsExpr := q.eps.1, epsApprox := q.eps.2,
    deltaExpr := aeDeltaExpr, deltaApprox := aeDeltaFloat,
    grade := q.grade, gradeExt := q.gradeExt, blocks := q.blocks,
    hypotheses := countHypotheses q.n q.m q.M, restoration := countRestorationText q.n q.m,
    predicateHash := q.predicateHash, circuitHash := Certify.circuitHash q.circuit,
    proofHash := none, gateCounts := Certify.gateCounts q.circuit, config := cfg, axioms := [],
    status := .notYetAudited, theoremName := none, obligations := [],
    frontEnd := frontEndProvedText, uncompute := q.mode }

/-- PHASE2_SPEC.md §A.4 (5), §A.5 (5′) — the status line of `cqr certify --problem count`: the
decided count, or "solution count not decided" with ε as its maximum over `a`. -/
def countStatusLine (q : CountRequest) (status : Status) (obligations : List String) : String :=
  match status with
  | .certified =>
    match q.M with
    | some M => s!"certified (ε ≈ {round6 (aeEpsFloat q.n M q.m)}, δ = 1 − 8/π² ≈ {round6 aeDeltaFloat}; \
        universal in M ≥ 1; M = {M} decided by the kernel)"
    | none => s!"certified (ε ≤ π/2^{q.m} + π²/4^{q.m} ≈ {round6 (aeEpsMaxFloat q.m)}, δ = 1 − 8/π² ≈ \
        {round6 aeDeltaFloat}; universal in M ≥ 1; solution count not decided)"
  | _ => s!"certificate with tracked obligations: {", ".intercalate obligations}"

/-! ## The run report (report §8.5.2, Table 8.5.2 shape) -/

/-- The data of one `cqr certify --problem count` run; `pattern`, `subst` and `sides` come from
the actual match of Algorithm 2 (Stage 21a3). -/
structure CountRunData where
  q : CountRequest
  source : String
  pattern : String
  /-- the substitution, rendered `F₁ ↦ 8, …` -/
  subst : String
  /-- the discharged side conditions, rendered -/
  sides : List String
  certPath : String
  timing : KernelTiming
  axioms : List String
  statusLine : String
  certified : Bool

/-- The sentence of amendment (4): the guarantee in units of `M`. -/
def mUnitsText (n M m : Nat) : String :=
  let eps := round6 (aeEpsFloat n M m)
  s!"with probability at least 8/π² ≈ {round6 (1 - aeDeltaFloat)}, the decoded estimate \
    sin²(π y/2^{m}) is within ε ≈ {eps} of a = M/2^{n}: in units of M, M within about \
    ± {mUnits n M m} (ε · 2^{n}, rounded); at M = {M} the decoding set contains the estimate 0 (the weak instance \
    PHASE2_SPEC §A.8 item 3 chose for size); the precision grows with m"

/-- The sentence of (5′) when the count is not decided: the guarantee for every `M ≥ 1`, with ε
at its maximum over `a`. -/
def mUnitsTextMax (n m : Nat) : String :=
  let eps := round6 (aeEpsMaxFloat m)
  s!"with probability at least 8/π² ≈ {round6 (1 - aeDeltaFloat)}, the decoded estimate \
    sin²(π y/2^{m}) is within ε ≤ π/2^{m} + π²/4^{m} ≈ {eps} (the maximum over a of ae_eps a {m}) of \
    a = M/2^{n}, for whatever the true count M ≥ 1 is: in units of M, M within about \
    ± {(aeEpsMaxFloat m * (2 ^ n : Nat).toFloat).round.toUInt64.toNat} (ε · 2^{n}, rounded); the \
    solution count is not decided (n = {n} above --count-limit); the precision grows with m"

/-- The statement sentence of a request: at the decided count, or the maximum of (5′). -/
def CountRequest.statement (q : CountRequest) : String :=
  match q.M with
  | some M => mUnitsText q.n M q.m
  | none => mUnitsTextMax q.n q.m

/-- Report §8.5.2 — the rows of Table 8.5.2 for a counting run (stage 1 split as in the Grover
report; stages 2 and 3 are the request parameter and the library entry that Stage 21 wires). -/
def CountRunData.rows (d : CountRunData) : List ReportRow :=
  let q := d.q
  let G := gateCounts q.circuit
  let g := q.grade
  let e := q.gradeExt
  let kms := match d.timing.kernelMs with | some k => s!"kernel {msText k}, " | none => ""
  let it0 := ((iterateBlocks q.blocks).headD default).circuit
  let blocks := ", ".intercalate (q.blocks.map fun b =>
    s!"{b.name} ×{b.mult} ({b.circuit.gates.length} gates, {gradeText (Synthesis.grade b.circuit)})")
  [ { stage := "1a. DSL Input: parser, surface checker",
      input := s!"{d.source} (predicate_hash {q.predicateHash.take 12}…)",
      output := s!"Typed AST `{q.name}`",
      verification := .declaredTrustBoundary, resources := "—",
      note := "parser, surface checker and the typed-term printer: declared trust boundary (the \
        theorem of 1b starts at the typed-term literal `prog` of Cert.lean, so an error before it \
        is not detected there); the source text is bound by predicate_hash only" },
    { stage := "1b. DSL Input: typed AST → network", input := s!"Typed AST `{q.name}`",
      output := "Boolean network (toNetwork)", verification := .kernelChecked,
      resources := s!"n = {q.n} input bits; `front_end` covers all 2^{q.n} = {2 ^ q.n} inputs (a \
        theorem, not an enumeration)",
      note := s!"typed AST → network: proved (`toNetwork_pred`, Stage 16a) and kernel-checked at \
        this instance in Cert.lean — `prog`, `prog_scoped` (decide), `net_ok : toNetwork prog = \
        .ok net` (decide +kernel), `front_end : ∀ x, evalProgram prog x = Network.pred net {q.n} \
        x`; declared as trust_boundary.front_end = \"{frontEndProvedText}\"" },
    { stage := "2. Spec Extraction", input := "Typed AST, request --problem count --precision m",
      output := s!"Counting request: Count, n = {q.n}, m = {q.m}, kmax = none (exact inverse QFT)",
      verification := .unverified,
      resources := match q.M with
        | some M => s!"M = {M} solutions (Network.countSat on all 2^{q.n} inputs, decided by the \
            kernel in Cert.lean: hM_count)"
        | none => s!"M not decided (n = {q.n} above --count-limit); `cert` holds for every M ≥ 1",
      note := "the problem class and the precision are request parameters (PHASE2_SPEC §A.5): \
        `SigmaIn.withProblem` sets the class Count and the seventh field m before the term is built; \
        the certificate theorem `cert` is universal in M and does not use the count" ++
        match q.M with
        | some _ => " — `cert_count` is its instance at the kernel-decided count"
        | none => " — the count is not decided, so there is no `cert_count` and ε is stated as its \
            maximum over a (PHASE2_SPEC §A.5 (5′))" },
    { stage := "3. Pattern Matching", input := "Counting request σ_in (seven fields)",
      output := s!"{d.pattern}: σ = {"{"}{d.subst}{"}"}",
      verification := .unverified,
      resources := s!"side conditions discharged: {if d.sides.isEmpty then "none" else
        "; ".intercalate d.sides}; M ≥ 1 in `cert`",
      note := "Algorithm 2 on the request term (Stage 21a1: the Count entry, F₆ : any); \
        `millerMatch_sound` and Proposition 5.1 (`matchLibrary_spec`, Stage 21a2) are proved for the \
        algorithm, this run is not kernel-checked; the builder dispatch goes through `qplpLibrary` \
        (Stage 21a3) and the certificate theorem states the counting instance directly" },
    { stage := "4. QPLP Instant.",
      input := s!"ae_parametric_lemma at n = {q.n}, m = {q.m}; blocks {blocks}",
      output := s!"Counting circuit H^⊗{q.n + q.m} · ∏_j ctrl_j(G)^(2^j) · QFT^−1 (`emitted` = \
        assembleCounting of the blocks in Cert.lean)",
      verification := .kernelChecked,
      resources := s!"grade {gradeText g} (composed bound, grade_assembleCounting_le); ε \
        {if q.M.isSome then "=" else "≤"} {q.eps.1} ≈ {round6 q.eps.2}, δ = {aeDeltaExpr} ≈ \
        {round6 aeDeltaFloat}; {gradeExtText e} (composed; T-depth a bound)",
      note := s!"every block as a literal with its `_ok` link, `grade_eq`, `gradeExt_eq` and \
        `liveEnd` by `decide +kernel`; `emitted_ok` by `countingCircuit_of_blocks` (no kernel \
        evaluation of the whole circuit); `grade_le` by `grade_assembleCounting_le` and `decide`; \
        {q.statement}{rotNote e}" },
    { stage := "5. Oracle Synthesis",
      input := s!"Boolean network ({q.net.nodes.size} nodes, {q.net.andCount} AND), controlled on \
        each phase qubit",
      output := "controlled U_P and controlled U_s inside every iterate block (Lemma 6.3.2 per \
        oracle call, countingCircuit_ancRestore)",
      verification := .kernelChecked,
      resources := s!"iterate block {gradeText (Synthesis.grade it0)}; \
        {(iterateBlocks q.blocks).length} distinct iterates, {2 ^ q.m - 1} copies",
      note := "the blocks' `_ok` links tie the literals to `controlledGrover net n m j`; the \
        restoration of every block is the library theorem `countingCircuit_ancRestore` (Stage \
        19c), applied inside `ae_parametric_lemma`" },
    { stage := "6. Ancilla Restore", input := "Controlled oracles and diffusions of the blocks",
      output := "Restored circuit (AncRestore conjunct of `cert`)",
      verification := .kernelChecked,
      resources := s!"{G.midCircuitMeasurements} MBU measurements, {G.classicallyControlled} \
        classically controlled gates; a = {g.a}",
      note := s!"AncRestore ({q.n} + {q.m}) emitted.nAnc emitted (U_count (net.pred {q.n}) {q.m} \
        none), on density operators (Lemma 6.3.2 per oracle call, the tree diffusion's MCZ, the \
        phase fix, the data-only inverse QFT: countingCircuit_ancRestore, Stage 19c)" },
    { stage := "7. Certificate Gen", input := "Proof + composed grade",
      output := match q.M with
        | some _ => s!"{d.certPath}, certificate.json (theorems {q.theoremName}, \
            {q.countTheoremName})"
        | none => s!"{d.certPath}, certificate.json (theorem {q.theoremName}; no cert_count: the \
            count is not decided)",
      verification := .kernelChecked,
      resources := s!"{kms}wall {msText d.timing.wallMs} ({d.timing.statistic}); axioms: \
        {", ".intercalate d.axioms}",
      note := s!"lake env lean exit 0; #print axioms audited for `cert`{if q.M.isSome then
        " and `cert_count`" else ""}; status: {d.statusLine}" },
    { stage := "8. QIR Export", input := "Internal circuit (`emitted`)",
      output := s!"QIR text ({q.name}.qir), OpenQASM 3 ({q.name}.qasm)",
      verification := .declaredTrustBoundary,
      resources := s!"G = {G.total} noisy operations ({G.unitary} unitary, \
        {G.midCircuitMeasurements} mid-circuit measurements, {G.classicallyControlled} \
        classically controlled, {G.terminalMeasurements} terminal measurements over all \
        {q.n} + {q.m} data qubits)",
      note := s!"emitter unverified; translation-validated by re-parse in tests/diff \
        (certify_check.py), not in this run; trust_boundary.emitted = QIR text; the inverse QFT's \
        cp gates are emitted to QIR as their five-gate decomposition (decomposeCp_unitary_wf) and \
        to OpenQASM 3 as cp; {countHardwareNote q.n q.m}" } ]

/-- Report §8.5.2 — the counting run report as Markdown. -/
def CountRunData.toMarkdown (d : CountRunData) : String :=
  let rows := d.rows
  let q := d.q
  let header := s!"# Run report: {q.name} (counting)\n\n\
    Report §8.5.2 (Table 8.5.2 shape), Stage 9b decision 4: every resource is a measured value \
    of this run, never a report target; the grade is the composed bound of Stage 19a \
    (PHASE2_SPEC §A.4, amendments before Stage 20b3).\n\n\
    - source: `{d.source}`\n- instance: n = {q.n}, m = {q.m}, kmax = none (exact inverse QFT), \
    {match q.M with
      | some M => s!"M = {M} (kernel-decided; `cert` is universal in M ≥ 1)"
      | none => s!"M not decided (n = {q.n} above --count-limit; `cert` is universal in M ≥ 1; ε \
          stated as its maximum over a)"}, uncompute = {q.mode}, shape tree\n\
    - what the certificate states: {q.statement}; it makes no claim for M = 0\n\
    - why m = {q.m}: the weak instance chosen for size (PHASE2_SPEC §A.8 item 3): every block \
    below 600 gates, the kernel check of the blocks in seconds; a sharper estimate needs more \
    phase qubits (the AQFT bound is vacuous for m ≤ 6, so no AQFT certificate here)\n\
    - status: **{d.statusLine}**\n\n\
    | Stage | Input | Output | Verification | Resources |\n|---|---|---|---|---|\n"
  let body := String.join (rows.map fun r =>
    s!"| {mdCell r.stage} | {mdCell r.input} | {mdCell r.output} | {r.verification.name} | \
      {mdCell r.resources} |\n")
  let notes := String.join ((rows.zipIdx.map fun (r, i) => s!"{i + 1}. {r.note}\n"))
  header ++ body ++ "\nWhat each status covers:\n\n" ++ notes

/-- Report §8.5.2 — the counting run report as JSON (`rows` in stage order). -/
def CountRunData.toJson (d : CountRunData) : Json :=
  let q := d.q
  Json.mkObj
    [("name", Json.str q.name), ("source", Json.str d.source), ("pattern", Json.str "Count"),
     ("instance", Json.mkObj [("n", q.n),
       ("M", match q.M with | some M => Lean.toJson M | none => Json.null), ("m", q.m),
       ("kmax", Json.null)]),
     ("status", Json.str d.statusLine), ("certified", Json.bool d.certified),
     ("statement", Json.str q.statement),
     ("rows", Json.arr (d.rows.map fun r => Json.mkObj
        [("stage", Json.str r.stage), ("input", Json.str r.input), ("output", Json.str r.output),
         ("verification", Json.str r.verification.name), ("resources", Json.str r.resources),
         ("note", Json.str r.note)]).toArray)]

end CQRV.Certify

end
