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
  of the theorem (§5.2.4, never decided);
* `#print axioms cert` (parsed by `CQRV.Certify.Audit`).

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

/-- The request of a matched Grover instance with solution count `M`. -/
def CertRequest.ofInstance (name src : String) (gi : GroverInstance) (M : Nat) : CertRequest :=
  { name, net := gi.net, n := gi.n, M, r := gi.r, circuit := gi.circuit,
    delta := groverDelta gi.r gi.n M, grade := gi.circuit.grade, nAnc := gi.circuit.nAnc,
    predicateHash := CQRV.Certify.predicateHash src }

/-- The namespace of the generated declarations. -/
def CertRequest.namespace (q : CertRequest) : String := s!"CQRV.Cert.«{q.name}»"

/-- The fully qualified name of the certificate theorem (as `#print axioms` prints it). -/
def CertRequest.theoremName (q : CertRequest) : String := s!"CQRV.Cert.{q.name}.cert"

/-- The predicate of the certificate statement. -/
def CertRequest.predText (q : CertRequest) : String := s!"(Network.pred net {q.n})"

/-- The statement of `cert`. -/
def CertRequest.statement (q : CertRequest) : String :=
  let g := q.grade
  s!"theorem cert
    (hM_card : (Finset.univ.filter fun x => Network.pred net {q.n} x = true).card = {q.M}) :
    RealizesExact (SearchSpec {q.predText}) (basisPOVM {q.n}) (groverChannel {q.n} emitted)
        {realLit q.delta} ⟨{g.w}, {g.d}, {g.t}, {g.a}⟩ ∧
      AncRestore {q.n} {q.nAnc} emitted (groverOp {q.predText} ^ {q.r} * hadamardU {q.n}) :="

/-- Report §5.1.3, §8.4.1, §8.4.4 — the text of `Cert.lean` (LF line endings). -/
def renderCert (q : CertRequest) : String :=
  let g := q.grade
  let header := s!"import CQRV

/-!
# Certificate `{q.name}` (generated by `cqr certify`; do not edit)

Report §5.1.3, §8.4.1, §8.4.4 (DECISIONS.md 2026-10-25, Stage 8b): the Grover parametric lemma
specialized to the request and checked by the Lean kernel (`lake env lean`). Instance:
n = {q.n}, M = {q.M} (hypothesis `hM_card`, never decided), r = {q.r}.
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

/-- Report §8.4.1, §8.4.4 — the certificate: the emitted circuit realizes the search spec of
`net` with δ = {q.delta} exactly within its measured grade, and restores its ancillae; conditional
on the solution count `hM_card`. -/
{q.statement}
  grover_certificate oracle mcz (by decide) emitted_ok delta_eq grade_eq nAnc_eq hM_card
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
