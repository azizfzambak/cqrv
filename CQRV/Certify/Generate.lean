module

public import CQRV.Certify.Certificate

/-!
# CQRV.Certify.Generate

Report §5.1.3 (a request is certified by specializing the parametric proof and kernel-checking
it, never by re-proving), §8.4.1 (specialization to concrete parameters), §8.4.4 (certificate
contents) — Stage 8b task 1, reviewer decision 1 (DECISIONS.md 2026-10-25): the text of
`certs/<name>/Cert.lean` for a matched Grover request.

The generated file imports `CQRV` and contains

* `net`: the network literal of the request (`toNetwork`), and `emitted`: the IR literal of the
  circuit `cqr certify` emits as QIR / OpenQASM 3 (and whose `circuit_hash` the JSON records);
* `emitted_ok : groverCircuit net n r = .ok emitted` by `decide +kernel` — the hash link: the
  kernel recomputes the synthesizer on `net` and compares with the literal, so the circuit the
  theorem is about is the emitted one;
* the oracle certificate (`synthesizeOracle net = .ok …`, `WF`) and the diffusion
  certificate of the MCZ on `n` qubits, every side condition by `decide +kernel`;
* `delta_eq`, `grade_eq`, `nAnc_eq` (kernel evaluation of `groverDelta`, `Synthesis.grade`,
  `Circuit.nAnc`);
* `theorem cert (hM_card : …)`: `grover_certificate` at these data — `hM_card` is a hypothesis
  of the theorem (§5.2.4), or, since Stage 14a (`CertRequest.count = .kernelDecided`, `cqr
  certify --count-limit k` with `n ≤ k`), `theorem hM_count : (Finset.univ.filter …).card = M`
  by `Network.countSat_eq_card` and `decide +kernel`, and `theorem cert` takes no hypothesis;
* `#print axioms cert` (parsed by `CQRV.Certify.Audit`).

Stage 12d (decision 4), Stage 13a′ (decision 2): for `cqr certify --shape few:log` the file
instead names the few-ancilla MCZ (`okPayload (mczFewK n .logDepth)`), proves
`mczFew n .logDepth = .ok …` and `diffusionFew n .logDepth = .ok Dc` by `decide +kernel`, and
applies `grover_certificate_few_all` (KG Theorem 5.1 for every `n`, Stage 13a): no per-instance
classical check (Stage 12d checked `fewCheck n a₀ (plan n .logDepth)` over `2ⁿ` inputs).

No `native_decide` is ever written (it adds `Lean.ofReduceBool`, which the audit rejects). Since
Stage 9a, Lemma 6.3.2 holds for networks with XOR nodes (`lemma_6_3_2_xor`), so every request
gets the same proved certificate and the generator writes no `sorry` (Stage 8b wrote the tracked
obligation `lemma_6_3_2_xor` for XOR networks).
-/

@[expose] public section

namespace CQRV.Certify

open CQRV CQRV.Synthesis

/-! ## Lean literals of the IR -/

/-- A qubit as a Lean term, `(.data 3)` / `(.anc 0)`. -/
def qubitLit : Qubit → String
  | .data i => s!"(.data {i})"
  | .anc i => s!"(.anc {i})"

/-- A gate as a Lean term of type `Gate`. -/
def gateLit : Gate → String
  | .h q => s!".h {qubitLit q}"
  | .s q => s!".s {qubitLit q}"
  | .sdg q => s!".sdg {qubitLit q}"
  | .t q => s!".t {qubitLit q}"
  | .tdg q => s!".tdg {qubitLit q}"
  | .x q => s!".x {qubitLit q}"
  | .z q => s!".z {qubitLit q}"
  | .cnot c t => s!".cnot {qubitLit c} {qubitLit t}"
  | .cz a b => s!".cz {qubitLit a} {qubitLit b}"
  | .measure q c => s!".measure {qubitLit q} {c}"
  | .ifBit c g => s!".ifBit {c} ({gateLit g})"
  | .alloc q => s!".alloc {qubitLit q}"
  | .free q => s!".free {qubitLit q}"

/-- Comma-separated items, `perLine` per line, continuation lines indented by `indent`. -/
def joinWrapped (items : List String) (perLine : Nat) (indent : String) : String :=
  String.join <| items.zipIdx.map fun (s, i) =>
    (if i == 0 then "" else if i % perLine == 0 then ",\n" ++ indent else ", ") ++ s

/-- A circuit as a Lean term of type `Circuit` (5 gates per line). -/
def circuitLit (C : Circuit) : String :=
  s!"⟨{C.nData}, [\n    {joinWrapped (C.gates.map gateLit) 5 "    "}]⟩"

/-- A network node as a Lean term of type `Network.Node`. -/
def nodeLit : Node → String
  | .input k => s!".input {k}"
  | .const b => s!".const {b}"
  | .not i => s!".not {i}"
  | .and i j => s!".and {i} {j}"
  | .xor i j => s!".xor {i} {j}"

/-- A network as a Lean term of type `Network`. -/
def networkLit (N : Network) : String :=
  s!"⟨{N.nInputs}, #[\n    {joinWrapped (N.nodes.toList.map nodeLit) 8 "    "}],\n  \
    {N.outputs}⟩"

/-- An exact rational `q ≥ 0` as a real literal, `(7 / 128 : ℝ)`. -/
def realLit (q : Rat) : String := s!"({q.num} / {q.den} : ℝ)"

/-- An exact rational as a `ℚ` literal, `(7 / 128 : ℚ)`. -/
def ratLit (q : Rat) : String := s!"({q.num} / {q.den} : ℚ)"

/-! ## The request -/

/-- Report §8.4.1 — what a certificate specializes: the request's name and source (for the
header), its network, the instance `(n, M, r)`, the emitted circuit, and the values the kernel
re-checks (exact δ, measured grade, ancilla count). -/
structure CertRequest where
  name : String
  net : Network
  n : Nat
  M : Nat
  r : Nat
  circuit : Circuit
  delta : Rat
  grade : Grade
  nAnc : Nat
  predicateHash : String
  /-- Stage 12d: the diffusion (`.tree` unless `--shape few:log`) -/
  diffusion : CertDiffusion := .tree
  /-- Stage 14a: `M` decided by the kernel (`hM_count`) or a hypothesis (`hM_card`) -/
  count : CountStatus := .hypothesis

/-- The request of a matched Grover instance with solution count `M`. -/
def CertRequest.ofInstance (name src : String) (gi : GroverInstance) (M : Nat)
    (count : CountStatus := .hypothesis) : CertRequest :=
  { name, net := gi.net, n := gi.n, M, r := gi.r, circuit := gi.circuit,
    delta := groverDelta gi.r gi.n M, grade := gi.circuit.grade, nAnc := gi.circuit.nAnc,
    predicateHash := CQRV.Certify.predicateHash src, diffusion := gi.diffusion, count }

/-- The namespace of the generated declarations. -/
def CertRequest.namespace (q : CertRequest) : String := s!"CQRV.Cert.«{q.name}»"

/-- The fully qualified name of the certificate theorem (as `#print axioms` prints it). -/
def CertRequest.theoremName (q : CertRequest) : String := s!"CQRV.Cert.{q.name}.cert"

/-- The predicate of the certificate statement. -/
def CertRequest.predText (q : CertRequest) : String := s!"(Network.pred net {q.n})"

/-- How the file header describes `M` (Stage 14a). -/
def CertRequest.countText (q : CertRequest) : String :=
  match q.count with
  | .kernelDecided => s!"M = {q.M} (decided by the kernel: `hM_count`, Stage 14a)"
  | .hypothesis => s!"M = {q.M} (hypothesis `hM_card`, never decided)"

/-- The solution-count fact `cert` is applied to: `hM_count` or the hypothesis `hM_card`. -/
def CertRequest.countArg (q : CertRequest) : String :=
  match q.count with
  | .kernelDecided => "hM_count"
  | .hypothesis => "hM_card"

/-- The last clause of the doc comment of `cert`. -/
def CertRequest.countClause (q : CertRequest) : String :=
  match q.count with
  | .kernelDecided => "the solution count is decided by the kernel (`hM_count`)"
  | .hypothesis => "conditional on the solution count `hM_card`"

/-- Report §8.2 (Stage 14a) — the theorem `hM_count` (`Network.countSat_eq_card`, then the
kernel evaluates `Network.countSat net n` on all `2ⁿ` inputs); empty when `M` stays a
hypothesis. -/
def CertRequest.countTheorem (q : CertRequest) : String :=
  match q.count with
  | .hypothesis => ""
  | .kernelDecided => s!"/-- Report §8.2 (Stage 14a) — the solution count, decided by the kernel: `Network.countSat`
evaluates `net` on all 2^{q.n} inputs; `Network.countSat_eq_card` identifies that count with the
cardinality of the statement. -/
theorem hM_count : (Finset.univ.filter fun x => Network.pred net {q.n} x = true).card = {q.M} := by
  rw [← Network.countSat_eq_card]
  decide +kernel

"

/-- The statement of `cert`: with the hypothesis `hM_card`, or (Stage 14a) without any
hypothesis when `hM_count` is proved. -/
def CertRequest.statement (q : CertRequest) : String :=
  let g := q.grade
  let hyp := match q.count with
    | .hypothesis =>
      s!"\n    (hM_card : (Finset.univ.filter fun x => Network.pred net {q.n} x = true).card = {q.M})"
    | .kernelDecided => ""
  s!"theorem cert{hyp} :
    RealizesExact (SearchSpec {q.predText}) (basisPOVM {q.n}) (groverChannel {q.n} emitted)
        {realLit q.delta} ⟨{g.w}, {g.d}, {g.t}, {g.a}⟩ ∧
      AncRestore {q.n} {q.nAnc} emitted (groverOp {q.predText} ^ {q.r} * hadamardU {q.n}) :="

/-- Report §5.1.3, §8.4.1, §8.4.4, §8.2 (Stage 12d decision 4, Stage 13a′ decision 2) — the text
of `Cert.lean` for the few-ancilla diffusion (`--shape few:log`, LF line endings). -/
def renderCertFew (q : CertRequest) : String :=
  let g := q.grade
  let n := q.n
  s!"import CQRV

/-!
# Certificate `{q.name}` (generated by `cqr certify --shape few:log`; do not edit)

Report §5.1.3, §8.4.1, §8.4.4 (DECISIONS.md 2026-10-25, Stage 8b; 2026-10-26, Stage 12d;
2026-10-28, Stage 13a′): the Grover parametric lemma over a certified diffusion
(`grover_parametric_lemma_diff`), specialized to the request with the few-ancilla diffusion
(candidate B: Khattar–Gidney 2025 §5.3, Maslov 2016 relative-phase Toffoli pairs, at most 2 clean
ancillae), and checked by the Lean kernel (`lake env lean`). Instance: n = {n},
{q.countText}, r = {q.r}. KG Theorem 5.1 for every n
(`mczFew_logDepth_ancRestore`, Stage 13a); no per-instance classical check.
predicate_hash = {q.predicateHash}
-/

namespace {q.namespace}

open CQRV CQRV.Synthesis CQRV.Grover CQRV.Certify

/-- The Boolean network of the request (`toNetwork`, §6.1.2). -/
def net : Network := {networkLit q.net}

/-- The emitted circuit (IR, §6.1.4): QIR / OpenQASM 3 and `circuit_hash` are of this literal. -/
def emitted : Circuit := {circuitLit q.circuit}

theorem delta_eq : ((groverDelta {q.r} {n} {q.M} : ℚ) : ℝ) = {realLit q.delta} := by
  rw [show groverDelta {q.r} {n} {q.M} = {ratLit q.delta} by decide +kernel]
  norm_num

theorem grade_eq : Synthesis.grade emitted = ⟨{g.w}, {g.d}, {g.t}, {g.a}⟩ := by decide +kernel

theorem nAnc_eq : emitted.nAnc = {q.nAnc} := by decide +kernel

/-- The synthesized oracle of `net`. -/
def oracleCircuit : Circuit := okPayload (synthesizeOracle net)

/-- The oracle certificate (§5.2.4): Lemma 6.3.2 fills its restoration field. -/
def oracle : OracleCert {n} where
  N := net
  C := oracleCircuit
  hn := rfl
  hC := except_eq_ok_okPayload (synthesizeOracle net) (by decide +kernel)
  hWF := by decide +kernel

/-- The few-ancilla MCZ on {n} qubits (Stage 12b candidate B; `mczFewK` is `mczFew` with a
kernel-evaluable sort, `mczFew_eq_K`). -/
def mczCircuit : Circuit := okPayload (mczFewK {n} .logDepth)

theorem mcz_ok : mczFew {n} .logDepth = .ok mczCircuit := by
  rw [mczFew_eq_K]
  exact except_eq_ok_okPayload (mczFewK {n} .logDepth) (by decide +kernel)

/-- The few-ancilla diffusion on {n} qubits (§8.2). -/
def diffCircuit : Circuit := diffusionCircuit {n} mczCircuit

theorem diff_ok : diffusionFew {n} .logDepth = .ok diffCircuit := diffusionFew_ok_of mcz_ok

/-- The hash link: the Grover circuit of `groverCircuitFew` is `groverCircuitOf` the oracle and
the diffusion; the kernel compares it with `emitted`. -/
theorem emitted_ok : groverCircuitFew net {n} {q.r} .logDepth = .ok emitted :=
  (groverCircuitFew_ok_of oracle.hn oracle.hC mcz_ok).trans (congrArg Except.ok (by decide +kernel))

{q.countTheorem}/-- Report §8.4.1, §8.4.4 — the certificate: the emitted circuit realizes the search spec of
`net` with δ = {q.delta} exactly within its measured grade, and restores its ancillae;
{q.countClause}. -/
{q.statement}
  grover_certificate_few_all oracle (by decide) diff_ok emitted_ok delta_eq grade_eq nAnc_eq
    {q.countArg}

#print axioms cert

end {q.namespace}
"

/-- Report §5.1.3, §8.4.1, §8.4.4 — the text of `Cert.lean` (LF line endings). -/
def renderCert (q : CertRequest) : String :=
  if q.diffusion == .fewLog then renderCertFew q else
  let g := q.grade
  let header := s!"import CQRV

/-!
# Certificate `{q.name}` (generated by `cqr certify`; do not edit)

Report §5.1.3, §8.4.1, §8.4.4 (DECISIONS.md 2026-10-25, Stage 8b): the Grover parametric lemma
specialized to the request and checked by the Lean kernel (`lake env lean`). Instance:
n = {q.n}, {q.countText}, r = {q.r}.
predicate_hash = {q.predicateHash}
-/

namespace {q.namespace}

open CQRV CQRV.Synthesis CQRV.Grover CQRV.Certify

/-- The Boolean network of the request (`toNetwork`, §6.1.2). -/
def net : Network := {networkLit q.net}

/-- The emitted circuit (IR, §6.1.4): QIR / OpenQASM 3 and `circuit_hash` are of this literal. -/
def emitted : Circuit := {circuitLit q.circuit}

/-- The hash link: the kernel re-runs the synthesizer on `net` and compares with `emitted`. -/
theorem emitted_ok : groverCircuit net {q.n} {q.r} = .ok emitted :=
  except_ok_of_check _ _ (by decide +kernel)

theorem delta_eq : ((groverDelta {q.r} {q.n} {q.M} : ℚ) : ℝ) = {realLit q.delta} := by
  rw [show groverDelta {q.r} {q.n} {q.M} = {ratLit q.delta} by decide +kernel]
  norm_num

theorem grade_eq : Synthesis.grade emitted = ⟨{g.w}, {g.d}, {g.t}, {g.a}⟩ := by decide +kernel

theorem nAnc_eq : emitted.nAnc = {q.nAnc} := by decide +kernel
"
  let body := s!"
/-- The synthesized oracle of `net`. -/
def oracleCircuit : Circuit := okPayload (synthesizeOracle net)

/-- The oracle certificate (§5.2.4): Lemma 6.3.2 fills its restoration field. -/
def oracle : OracleCert {q.n} where
  N := net
  C := oracleCircuit
  hn := rfl
  hC := except_eq_ok_okPayload (synthesizeOracle net) (by decide +kernel)
  hWF := by decide +kernel

/-- The MCZ of the V1 diffusion on {q.n} qubits (balanced AND tree, Stage 12a). -/
def mczCircuit : Circuit := okPayload (synthesizeOracle (treeNet {q.n}))

/-- The diffusion certificate `DiffusionCert {q.n}` (§8.2; `hPred` by `treeNet_pred`). -/
def mcz : DiffusionCert {q.n} where
  net := treeNet {q.n}
  mcz := {lb}N := treeNet {q.n}, C := mczCircuit, hn := rfl,
           hC := except_eq_ok_okPayload (synthesizeOracle (treeNet {q.n})) (by decide +kernel),
           hWF := by decide +kernel{rb}
  hN := rfl

{q.countTheorem}/-- Report §8.4.1, §8.4.4 — the certificate: the emitted circuit realizes the search spec of
`net` with δ = {q.delta} exactly within its measured grade, and restores its ancillae;
{q.countClause}. -/
{q.statement}
  grover_certificate oracle mcz (by decide) emitted_ok delta_eq grade_eq nAnc_eq {q.countArg}
"
  header ++ body ++ s!"
#print axioms cert

end {q.namespace}
"
where
  lb := "{"
  rb := "}"

end CQRV.Certify

end
