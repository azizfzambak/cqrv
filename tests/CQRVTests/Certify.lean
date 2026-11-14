module

import CQRV.Certify.Basic
import CQRV.Certify.Specialize
import CQRV.Emit.Basic
meta import CQRV.Certify.Basic
meta import CQRV.Emit.Basic

/-!
# Tests for `CQRV.Certify` and `CQRV.Emit` (Stage 8a; report §8.4.2–8.4.4, §9.5.3, §5.3)

SHA3-256 on the reviewer's vectors (the 200-string differential against hashlib is
`tests/diff/sha3_diff.py`), the exact δ, the sample certificate of grover_pred_037 (no kernel
check: `status` "not yet audited"; the schema check is `tests/diff/cert_schema.py`) and the shape
of the emitted QIR / QASM (the re-parse is `tests/diff/emit_diff.py`).

Stage 8b (report §5.1.3, §8.4.1, §9.5.1, §9.5.3): `auditAxioms`, the parsers of Lean's
`#print axioms` and profiler output, the shape of the generated `Cert.lean`, the axioms of the
lemmas a certificate instantiates (pinned with `#guard_msgs`). The kernel check itself and the
negative tests are `tests/diff/certify_check.py` (driver `scripts/check_certify.sh`).

Stage 14a (report §8.2): `Network.countSat` on the corpus, its agreement with the `Finset`
cardinality decided by the kernel on the committed network literal, and the shape of a
certificate whose solution count is kernel-decided (`hM_count`, `cert` without hypothesis).

Stage 17b (PHASE2_SPEC.md §A.1): schema 1.9.0 with `grade_ext`; `gradeExt_eq` right after
`grade_eq` in every template; the sample circuit `Emit.sampleCircuit` (every gate constructor)
and its OpenQASM 3 / QIR texts (`p(2*pi*a/N)`, `rz` with a hex-float angle, the five-gate `cp`,
the `rz` declaration only when used); `sampleCircuitIfCp` refused by the QIR emitter
(`unsupported_in_qir`); the Grover QIR / QASM texts unchanged (no `rz`).
-/

namespace CQRV.Tests.Certify

open CQRV CQRV.Certify CQRV.Emit CQRV.DSL CQRV.Synthesis

/-! ## SHA3-256 (decision 1) -/

#guard SHA3.sha3String "" == "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
#guard SHA3.sha3String "abc" == "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
-- the padding is one block for 135 bytes (single pad byte 0x86) and two for 136
#guard (SHA3.pad (ByteArray.mk (Array.replicate 135 0))).size == 136
#guard (SHA3.pad (ByteArray.mk (Array.replicate 135 0))).get! 135 == 0x86
#guard (SHA3.pad (ByteArray.mk (Array.replicate 136 0))).size == 272

/-! ## Exact δ (task 2) -/

-- sin²(5θ) for sin²θ = 1/8 (DECISIONS.md 2026-10-24, "the certified δ is exact")
#guard groverSuccess 2 (1 / 8) == 121 / 128
#guard toString (groverDelta 2 8 32) == "7/128"
-- r = 0: sin²θ; r = 1: sin²(3θ) = s(3 − 4s)²
#guard groverSuccess 0 (1 / 8) == 1 / 8
#guard groverSuccess 1 (1 / 8) == (1 / 8) * (3 - 4 * (1 / 8)) ^ 2
-- the closed form of the r = 2 case, s(5 − 20s + 16s²)², at s = 1/4, 1/3
#guard [(1 : Rat) / 4, 1 / 3].all fun s => groverSuccess 2 s == s * (5 - 20 * s + 16 * s ^ 2) ^ 2

/-! ## Sample certificate (task 2) -/

def groverSrc : String := include_str "../../examples/grover_pred_037.cqr"

def cfg : RefConfig := { lean := "leanprover/lean4:v4.35.0", mathlib := "m", physlib := "p" }

def sample : Except String Certificate := certificateOf groverSrc cfg

#guard match sample with
  | .ok c => c.delta == 7 / 128 && c.grade == ⟨15, 134, 72, 7⟩ && c.status == .notYetAudited &&
      c.n == 8 && c.M == 32 && c.r == 2 && c.proofHash.isNone && c.axioms.isEmpty &&
      c.count == .hypothesis
  | .error _ => false
-- Stage 14a: the sample (no kernel check) lists M under `hypotheses`; a kernel-decided one does not
#guard match sample with
  | .ok c => c.hypotheses.head? == some "solution_count = 32 (hM_card, supplied, not decided)" &&
      (c.toJson.compress.splitOn "\"solution_count\":{\"status\":\"hypothesis\",\"value\":32}").length == 2 &&
      (c.toJson.compress.splitOn "\"schema_version\":\"1.10.0\"").length == 2 &&
      (c.toJson.compress.splitOn "\"grade_kind\":\"measured\"").length == 2
  | .error _ => false
-- Stage 17b: the second record, measured from the circuit, as `grade_ext` (keys sorted)
#guard match sample with
  | .ok c => c.gradeExt == ⟨126, 39, 0, 18, 36⟩ &&
      (c.toJson.compress.splitOn
        "\"grade_ext\":{\"ff\":36,\"meas\":18,\"rot\":0,\"t_depth\":39,\"two_qubit\":126}").length == 2
  | .error _ => false
-- Stage 16b: the sample declares the proved front end
#guard match sample with
  | .ok c => c.frontEnd == frontEndProvedText &&
      (c.toJson.compress.splitOn ("\"front_end\":" ++ frontEndProvedText.quote)).length == 2
  | .error _ => false
-- Stage 8a review: G counts every noisy operation, terminal measurements included
#guard match sample with
  | .ok c => c.gateCounts == ⟨328, 18, 36, 8⟩ && c.gateCounts.total == 390
  | .error _ => false
-- LF normalization: the hash does not depend on the platform's line endings
#guard predicateHash groverSrc == predicateHash (groverSrc.replace "\n" "\r\n")

/-! ## Emitters (tasks 3, 4) -/

def groverC : Circuit :=
  match (parse groverSrc >>= check >>= toNetwork) >>= fun N => groverCircuit N 8 2 with
  | .ok C => C
  | .error _ => default

def qir : String := (emitQIR "grover_pred_037" groverC).toOption.getD ""

#guard (qir.splitOn "\"qir_profiles\"=\"adaptive_profile\"").length == 2
#guard (qir.splitOn "\"required_num_qubits\"=\"15\"").length == 2
#guard (qir.splitOn "\nmeasurements:\n").length == 2
/-- The terminal `measurements:` block (up to its branch to `output`). -/
def terminalBlock : String :=
  ((qir.splitOn "\nmeasurements:\n")[1]!.splitOn "\n  br label %output").head!

-- exactly 8 `mz` calls in the terminal block, on the data qubits 0..7
#guard (terminalBlock.splitOn "__quantum__qis__mz__body").length == 9
#guard (List.range 8).all fun i =>
  (terminalBlock.splitOn s!"mz__body(ptr inttoptr (i64 {i} to ptr)").length == 2
#guard (emitQASM "grover_pred_037" groverC).endsWith "out = measure x;\n"
-- Stage 17b: no phase gate in a synthesized circuit, so no `rz` and no `rz` declaration
#guard (qir.splitOn "rz").length == 1
#guard (qir.splitOn "declare void @__quantum__qis__cz__body(ptr, ptr)\ndeclare void @__quantum__qis__mz__body").length == 2

/-! ## Stage 17b — the sample circuit and the phase gates in both emitters (PHASE2_SPEC.md §A.1) -/

#guard sampleCircuit.validate.toOption.isSome
#guard sampleCircuitIfCp.validate.toOption.isSome
#guard sampleCircuit.nData == 3 && sampleCircuit.nAnc == 1 && sampleCircuit.nBits == 1
-- every constructor at least once; the measured record: 2Q = 6, rot = 3 (`p (-3) 5`, `cp 1 2`,
-- `cp (-1) 3`; `p 2 4` is a T-power, `cp 1 1` and `p 0 5` are Clifford), meas = 1, ff = 4
#guard sampleCircuit.gates.countP Gate.isTwoQubit == 6
#guard sampleCircuit.gradeExt.rot == 3 && sampleCircuit.gradeExt.meas == 1 &&
  sampleCircuit.gradeExt.ff == 4
#guard (["alloc", "h", "s", "sdg", "t", "tdg", "x", "z", "cnot", "cz", "p", "cp", "measure", "free"]
  : List String).all fun op =>
    sampleCircuit.gates.any fun g => (sampleCircuit.gateJson g).getObjValAs? String "op" == .ok op
#guard sampleCircuit.gates.any fun g => match g with | .ifBit _ (.p ..) => true | _ => false
#guard !sampleCircuit.gates.any fun g => match g with | .ifBit _ (.cp ..) => true | _ => false
#guard sampleCircuitIfCp.gates.any fun g => match g with | .ifBit _ (.cp 1 1 _ _) => true | _ => false

def sampleQasm : String := emitQASM "sample" sampleCircuit

#guard (sampleQasm.splitOn "p(2*pi*1/8) x[0];\n").length == 2
#guard (sampleQasm.splitOn "p(2*pi*(-3)/32) x[1];\n").length == 2
#guard (sampleQasm.splitOn "p(2*pi*2/16) x[2];\n").length == 2
#guard (sampleQasm.splitOn "p(2*pi*0/32) anc[0];\n").length == 2
#guard (sampleQasm.splitOn "cp(2*pi*1/2) x[0], x[1];\n").length == 2
#guard (sampleQasm.splitOn "cp(2*pi*(-1)/8) x[2], anc[0];\n").length == 2
#guard (sampleQasm.splitOn "if (c[0]) { p(2*pi*1/2) x[0]; }\n").length == 2
#guard (sampleQasm.splitOn "if (c[0]) { p(2*pi*1/4) x[1]; }\n").length == 2
#guard ((emitQASM "s" sampleCircuitIfCp).splitOn "if (c[0]) { cp(2*pi*1/2) x[1], x[2]; }\n").length == 2
#guard (sampleQasm.splitOn "unsupported").length == 1

def sampleQir : String := (emitQIR "sample" sampleCircuit).toOption.getD ""

-- the hex-float angles: π/4 for `p 1 3` and `p 2 4`, −3π/16 for `p (-3) 5`, 0 for `p 0 5`
#guard qirAngle 1 3 == "0x3FE921FB54442D18"
#guard qirAngle 2 4 == "0x3FE921FB54442D18"
#guard qirAngle 0 5 == "0x0000000000000000"
#guard qirAngle (-3) 5 == "0xBFE2D97C7F3321D2"
#guard qirAngle 1 1 == "0x400921FB54442D18"
#guard (sampleQir.splitOn "  call void @__quantum__qis__rz__body(double 0x3FE921FB54442D18, ptr inttoptr (i64 0 to ptr))\n").length == 2
#guard (sampleQir.splitOn "declare void @__quantum__qis__rz__body(double, ptr)\n").length == 2
-- `cp 1 1 x0 x1` is the five calls rz(π/2) x0; rz(π/2) x1; cnot; rz(−π/2) x1; cnot
#guard (sampleQir.splitOn ("  call void @__quantum__qis__rz__body(double 0x3FF921FB54442D18, ptr inttoptr (i64 0 to ptr))\n" ++
  "  call void @__quantum__qis__rz__body(double 0x3FF921FB54442D18, ptr inttoptr (i64 1 to ptr))\n" ++
  "  call void @__quantum__qis__cnot__body(ptr inttoptr (i64 0 to ptr), ptr inttoptr (i64 1 to ptr))\n" ++
  "  call void @__quantum__qis__rz__body(double 0xBFF921FB54442D18, ptr inttoptr (i64 1 to ptr))\n" ++
  "  call void @__quantum__qis__cnot__body(ptr inttoptr (i64 0 to ptr), ptr inttoptr (i64 1 to ptr))\n")).length == 2
#guard (sampleQir.splitOn "unsupported").length == 1
#guard (sampleQir.splitOn "\"required_num_qubits\"=\"4\"").length == 2
-- a classically controlled cp: refused with the diagnostic, nothing emitted
#guard match emitQIR "s" sampleCircuitIfCp with
  | .error d => d.stage == .emit && d.code == .unsupportedInQir &&
      d.message.startsWith "classically controlled cp has no QIR form in this emitter" &&
      (d.toJson.compress.splitOn "\"code\":\"unsupported_in_qir\"").length == 2 &&
      (d.toJson.compress.splitOn "\"stage\":\"emit\"").length == 2
  | .ok _ => false
#guard findIfCp sampleCircuit.gates == none
#guard (findIfCp sampleCircuitIfCp.gates).map (·.1) == some (sampleCircuit.gates.length - 1)

/-! ## Axiom audit (Stage 8b, decision 3) -/

#guard auditAxioms ["propext", "Classical.choice", "Quot.sound"] == .pass
#guard auditAxioms [] == .pass
#guard auditAxioms ["propext", "sorryAx", "Quot.sound"] == .fail ["sorryAx"]
#guard auditAxioms ["Lean.ofReduceBool"] == .fail ["Lean.ofReduceBool"]
#guard auditAxioms ["propext", "nAnc_eq._native.native_decide.ax_1_1"] ==
  .fail ["nAnc_eq._native.native_decide.ax_1_1"]
-- the trust-boundary table is empty today
#guard trustBoundary.isEmpty

/-! ## Parsers of the Lean output (decision 2) -/

#guard parseAxioms "T.cert" "'T.cert' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
  == some ["propext", "Classical.choice", "Quot.sound"]
-- long lists are wrapped by Lean's formatter
#guard parseAxioms "T.cert" "x\n'T.cert' depends on axioms: [propext,\n Classical.choice,\r\n sorryAx]\ny"
  == some ["propext", "Classical.choice", "sorryAx"]
#guard parseAxioms "T.cert" "'T.cert' does not depend on any axioms\n" == some []
#guard parseAxioms "T.cert" "'U.cert' depends on axioms: [propext]" == none
#guard parseAxioms "T.cert" "" == none
#guard parseAxioms "T.cert"
  "'T.cert' depends on axioms: [propext]\n'T.cert' depends on axioms: [propext]" == none
#guard parseProfilerMs "7.65s" == some 7650
#guard parseProfilerMs "163ms" == some 163
#guard parseProfilerMs "0.0683ms" == some 0
#guard parseProfilerMs "12μs" == some 0
#guard parseKernelMs "type checking took 7.03s\ncumulative profiling times:\n\ttype checking 7.65s\n"
  == some 7650

/-! ## The generated certificate (task 1) -/

/-- The certificate request of grover_pred_037 (`r = r⋆ = 2`, `M = 32`). -/
def groverReq : Option CertRequest :=
  match parse groverSrc >>= check with
  | .ok tp =>
    match groverInstance tp (extract tp) none with
    | .ok gi => some (CertRequest.ofInstance tp groverSrc gi 32)
    | .error _ => none
  | .error _ => none

def groverCert : String := (groverReq.map renderCert).getD ""

/-- A two-input XOR network. -/
def xorNet : Network := ⟨2, #[.input 0, .input 1, .xor 0 1], [2]⟩

#guard groverReq.map (·.theoremName) == some "CQRV.Cert.grover_pred_037.cert"
#guard (groverCert.splitOn "theorem cert").length == 2
#guard (groverCert.splitOn "native_decide").length == 1
#guard (groverCert.splitOn "sorry").length == 1
#guard (groverCert.splitOn "#print axioms cert").length == 2
#guard (groverCert.splitOn "(7 / 128 : ℝ) ⟨15, 134, 72, 7⟩").length == 2
-- Stage 12a: the generated diffusion certificate is the balanced tree
#guard (groverCert.splitOn "  net := treeNet 8").length == 2
#guard (groverCert.splitOn "theorem emitted_ok : groverCircuit net 8 2 = .ok emitted").length == 2
-- Stage 17b: `gradeExt_eq` right after `grade_eq`, every template (the few / coherent ones below)
def gradeExtFrag (e : GradeExt) : String :=
  s!"theorem gradeExt_eq : Synthesis.gradeExt emitted = ⟨{e.twoQ}, {e.tDepth}, {e.rot}, {e.meas}, {e.ff}⟩ := by decide +kernel\n\ntheorem nAnc_eq"
#guard groverReq.map (·.gradeExt) == some ⟨126, 39, 0, 18, 36⟩
#guard (groverCert.splitOn "⟨15, 134, 72, 7⟩ := by decide +kernel\n\n/-- PHASE2_SPEC.md §A.1 (Stage 17b)").length == 2
#guard (groverCert.splitOn (gradeExtFrag ⟨126, 39, 0, 18, 36⟩)).length == 2
#guard (groverCert.splitOn "gradeExt_eq").length == 2
-- Stage 16b: the front-end declarations between `net` and `emitted` (every template below too)
def progBlockFrags : List String :=
  ["  [9]⟩\n\n/-- The typed term of the request",
   "def prog : DSL.TypedProgram :=\n  { name := \"grover_pred_037\", params := [(\"x\", (.vec 8))], \
    ret := .bool,\n    body := (.letE (σ := .bool) \"b0\" (.idx (n := 8) (.var \"x\" (.vec 8)) \
    (.lit ⟨0, by decide⟩))",
   "theorem prog_scoped : prog.scoped = true := by decide\n",
   "theorem net_ok : toNetwork prog = .ok net := except_ok_of_check _ _ (by decide +kernel)\n",
   "theorem front_end : ∀ x : Fin 8 → Bool, DSL.evalProgram prog x = Network.pred net 8 x :=\n  \
    fun x => (toNetwork_pred prog net net_ok prog_scoped x).symm\n",
   "#print axioms front_end\n\n/-- The emitted circuit"]
#guard progBlockFrags.all fun f => (groverCert.splitOn f).length == 2
#guard (groverCert.splitOn "def prog").length == 2
-- Stage 9a: an XOR network gets the same proved certificate as an AND/NOT/OR network (oracle
-- certificate, no `sorry`, no `xorFree` side condition)
#guard groverReq.all fun q => ((renderCert { q with net := xorNet }).splitOn "sorry").length == 1
#guard groverReq.all fun q =>
  ((renderCert { q with net := xorNet }).splitOn "def oracle : OracleCert 8 where").length == 2
#guard (groverCert.splitOn "hXor").length == 1
-- Stage 14a: the default request keeps the hypothesis `hM_card`; with `count := .kernelDecided`
-- the certificate proves `hM_count` (`Network.countSat_eq_card`, `decide +kernel`) and `cert`
-- takes no hypothesis
#guard (groverCert.splitOn "\n    (hM_card : (Finset.univ.filter fun x => Network.pred net 8 x = true).card = 32) :").length == 2
#guard (groverCert.splitOn "hM_count").length == 1
#guard (groverCert.splitOn "nAnc_eq hM_card\n").length == 2
def groverCertCounted : String :=
  (groverReq.map fun q => renderCert { q with count := .kernelDecided }).getD ""
#guard (groverCertCounted.splitOn "theorem hM_count : (Finset.univ.filter fun x => Network.pred net 8 x = true).card = 32 := by\n  rw [← Network.countSat_eq_card]\n  decide +kernel\n").length == 2
#guard (groverCertCounted.splitOn "theorem cert :\n    RealizesExact").length == 2
#guard (groverCertCounted.splitOn "hM_card").length == 1
#guard (groverCertCounted.splitOn "nAnc_eq hM_count\n").length == 2
#guard (groverCertCounted.splitOn "native_decide").length == 1
#guard (groverCertCounted.splitOn "sorry").length == 1
-- Stage 12d: `--shape few:log` — the few-ancilla Grover circuit, its own template
def groverReqFew : Option CertRequest :=
  match parse groverSrc >>= check with
  | .ok tp =>
    match groverInstance tp (extract tp) none .fewLog with
    | .ok gi => some (CertRequest.ofInstance tp groverSrc gi 32)
    | .error _ => none
  | .error _ => none

def groverCertFew : String := (groverReqFew.map renderCert).getD ""

#guard groverReqFew.map (fun q => (q.grade, q.nAnc, q.diffusion)) ==
  some (⟨10, 172, 96, 2⟩, 2, .fewLog)
#guard groverReqFew.map (·.gradeExt) == some ⟨106, 77, 0, 8, 16⟩
#guard (groverCertFew.splitOn (gradeExtFrag ⟨106, 77, 0, 8, 16⟩)).length == 2
#guard progBlockFrags.all fun f => (groverCertFew.splitOn f).length == 2
#guard (groverCertFew.splitOn "native_decide").length == 1
#guard (groverCertFew.splitOn "sorry").length == 1
-- Stage 13a′: no per-instance classical check; `grover_certificate_few_all`
#guard (groverCertFew.splitOn "fewCheck").length == 1
#guard (groverCertFew.splitOn "classical_step").length == 1
#guard (groverCertFew.splitOn "mcz_WF").length == 1
#guard (groverCertFew.splitOn "diff_WF").length == 1
#guard (groverCertFew.splitOn "theorem mcz_ok : mczFew 8 .logDepth = .ok mczCircuit").length == 2
#guard (groverCertFew.splitOn "theorem emitted_ok : groverCircuitFew net 8 2 .logDepth = .ok emitted").length == 2
#guard (groverCertFew.splitOn "theorem diff_ok : diffusionFew 8 .logDepth = .ok diffCircuit").length == 2
#guard (groverCertFew.splitOn "  grover_certificate_few_all oracle (by decide) diff_ok emitted_ok").length == 2
#guard (groverCertFew.splitOn "  grover_certificate_few oracle").length == 1
#guard (groverCertFew.splitOn "(7 / 128 : ℝ) ⟨10, 172, 96, 2⟩").length == 2
#guard (groverCertFew.splitOn "treeNet").length == 1

/-! ## Stage 15b — `--uncompute coherent` (PHASE2_SPEC.md §A.0.1): its own template -/

def groverReqCoh : Option CertRequest :=
  match parse groverSrc >>= check with
  | .ok tp =>
    match groverInstance tp (extract tp) none .tree .coherent with
    | .ok gi => some (CertRequest.ofInstance tp groverSrc gi 32)
    | .error _ => none
  | .error _ => none

def groverCertCoh : String := (groverReqCoh.map renderCert).getD ""

-- the coherent instance: grade (15, 200, 144, 7), 7 ancillae, tree diffusion, mode coherent
#guard groverReqCoh.map (fun q => (q.grade, q.nAnc, q.diffusion, q.uncompute)) ==
  some (⟨15, 200, 144, 7⟩, 7, .tree, .coherent)
#guard groverReqCoh.map (·.circuit.nBits) == some 0
#guard groverReqCoh.map (·.gradeExt) == some ⟨216, 74, 0, 0, 0⟩
#guard (groverCertCoh.splitOn (gradeExtFrag ⟨216, 74, 0, 0, 0⟩)).length == 2
#guard progBlockFrags.all fun f => (groverCertCoh.splitOn f).length == 2
#guard (groverCertCoh.splitOn
  "theorem emitted_ok : groverCircuit net 8 2 none .tree .coherent = .ok emitted").length == 2
#guard (groverCertCoh.splitOn "def oracle : OracleCertCoh 8 where").length == 2
#guard (groverCertCoh.splitOn "def oracleCircuit : Circuit := okPayload (synthesizeOracle net .coherent)").length == 2
#guard (groverCertCoh.splitOn "  grover_certificate_coherent oracle (by decide) emitted_ok delta_eq \
  grade_eq nAnc_eq hM_card").length == 2
#guard (groverCertCoh.splitOn "(7 / 128 : ℝ) ⟨15, 200, 144, 7⟩").length == 2
#guard (groverCertCoh.splitOn "uncompute = coherent").length == 2
-- no diffusion-certificate literal, no measurement in the emitted literal, no sorry
#guard (groverCertCoh.splitOn "DiffusionCert").length == 1
#guard (groverCertCoh.splitOn "treeNet").length == 1
#guard (groverCertCoh.splitOn ".measure ").length == 1
#guard (groverCertCoh.splitOn ".ifBit ").length == 1
#guard (groverCertCoh.splitOn "native_decide").length == 1
#guard (groverCertCoh.splitOn "sorry").length == 1
-- with the kernel-decided count: `hM_count`, `cert` without hypothesis
#guard (((groverReqCoh.map fun q => renderCert { q with count := .kernelDecided }).getD "").splitOn
  "nAnc_eq hM_count\n").length == 2
-- the mbu request is the Phase 1 template, byte for byte (the default mode)
#guard groverReq.map (·.uncompute) == some .mbu
#guard groverReq.map (fun q => renderCert q == renderCert { q with uncompute := .mbu }) == some true
#guard groverReq.map (fun q => renderCert q != renderCert { q with uncompute := .coherent }) ==
  some true
-- `few:log` with `coherent` is `unsupported_combination`
#guard match parse groverSrc >>= check with
  | .ok tp =>
    match groverInstance tp (extract tp) none .fewLog .coherent with
    | .error (.diagnostic d) => d.stage == .synthesis && d.code == .unsupportedCombination
    | _ => false
  | .error _ => false
-- the JSON (Stage 16b, schema 1.8.0; 1.9.0 since Stage 17b; 1.10.0 with grade_kind "measured" since
-- Stage 21a3): `uncompute` written in every certificate, one version
#guard match sample with
  | .ok c =>
    let cc : Certificate := { c with uncompute := .coherent }
    (c.toJson.compress.splitOn "\"uncompute\":\"mbu\"").length == 2 &&
      (c.toJson.compress.splitOn "\"schema_version\":\"1.10.0\"").length == 2 &&
      (cc.toJson.compress.splitOn "\"uncompute\":\"coherent\"").length == 2 &&
      (cc.toJson.compress.splitOn "\"schema_version\":\"1.10.0\"").length == 2
  | .error _ => false
#guard (groverCertFew.splitOn "nAnc_eq\n    hM_card\n").length == 2
-- Stage 14a, few:log with the kernel-decided count
#guard (((groverReqFew.map fun q => renderCert { q with count := .kernelDecided }).getD "").splitOn
  "nAnc_eq\n    hM_count\n").length == 2
#guard (((groverReqFew.map fun q => renderCert { q with count := .kernelDecided }).getD "").splitOn
  "hM_card").length == 1

/-! ## The solution count decided by the kernel (Stage 14a, report §8.2) -/

def aluSrc : String := include_str "../../examples/simple_alu_x0_1.cqr"

/-- `Network.countSat` of a corpus predicate. -/
def countOf (src : String) (n : Nat) : Option Nat :=
  ((parse src >>= check >>= toNetwork).map (·.countSat n)).toOption

#guard countOf groverSrc 8 == some 32
#guard countOf aluSrc 6 == some 30
#guard xorNet.countSat 2 == 2
#guard xorNet.countSat 3 == 4
-- the network literal of the committed certificate examples/certs/grover_pred_037/Cert.lean,
-- counted by the kernel exactly as `hM_count` does
def groverNetLit : Network := ⟨8, #[.input 0, .input 1, .input 2, .input 3, .input 4, .input 5,
  .input 6, .input 7, .and 0 3, .and 8 7], [9]⟩
example : groverNetLit.countSat 8 = 32 := by decide +kernel
example : (Finset.univ.filter fun x => Network.pred groverNetLit 8 x = true).card = 32 := by
  rw [← Network.countSat_eq_card]
  decide +kernel
-- `bitsEquiv` is the bit vector of `inputBits` (bit `i` of `k` at index `i`)
#guard (List.finRange (2 ^ 3)).all fun k =>
  (List.finRange 3).all fun i => bitsEquiv 3 k i == (k.val >>> i.val % 2 == 1)

/-! ## `symDiff` by structural insertion sort (kernel-evaluable, Stage 8b) -/

#guard symDiff [.anc 2, .data 1, .data 0] [.data 1, .anc 0] == [.data 0, .anc 0, .anc 2]
#guard symDiff [] [.anc 1, .data 3, .anc 0] == [.data 3, .anc 0, .anc 1]
example : symDiff [.anc 1, .data 0] [.data 2] = [.data 0, .data 2, .anc 1] := by decide +kernel

/-! ## Hardware profiles (Stage 11b, §3.3.2–3.3.3)

`profileOfJson` on inline profile texts (the file `profiles/illustrative_sc.json` itself is read by
`tests/diff/certify_check.py` through `cqr certify --profile illustrative_sc`). -/

/-- The source entries of a profile, all eight fields. -/
def sourceAll : String :=
  "{\"w\":\"x\",\"d\":\"x\",\"t\":\"x\",\"a\":\"x\",\"t_gate_ns\":\"x\",\"t_T_ns\":\"x\",\
    \"t1_ns\":\"x\",\"p_bar\":\"x\"}"

/-- A profile text with the given budget `d`, `p_bar` and `source`. -/
def profileText (d pBar : String) (src : String := sourceAll) : String :=
  "{\"schema_version\":\"1.0.0\",\"name\":\"p\",\"source\":" ++ src ++
    ",\"budget\":{\"w\":127,\"d\":" ++ d ++ ",\"t\":null,\"a\":127},\"t_gate_ns\":500,\
    \"t_T_ns\":null,\"t1_ns\":100000,\"p_bar\":" ++ pBar ++ "}"

/-- Parse a profile text. -/
def readProfile (s : String) : Except String Profile := Lean.Json.parse s >>= profileOfJson

#guard match readProfile (profileText "200" "\"0.01\"") with
  | .ok p => p.budget == ⟨some 127, some 200, none, some 127⟩ && p.pBar == some (1 / 100) &&
      p.tGateNs == some 500 && p.tTNs == none && p.t1Ns == some 100000
  | .error _ => false
#guard match readProfile (profileText "null" "null") with
  | .ok p => p.budget.d == none && p.pBar == none
  | .error _ => false
-- rejected: p̄ > 1, p̄ as a number, a negative budget, a missing source entry, an unknown key
#guard (readProfile (profileText "200" "\"1.5\"")).toBool == false
#guard (readProfile (profileText "200" "0.01")).toBool == false
#guard (readProfile (profileText "-1" "\"0.01\"")).toBool == false
#guard (readProfile (profileText "200" "\"0.01\"" "{\"w\":\"x\"}")).toBool == false
#guard (readProfile ((profileText "200" "\"0.01\"").replace "\"name\"" "\"x\":1,\"name\"")).toBool
  == false
#guard profilePath "illustrative_sc" == "profiles/illustrative_sc.json"
-- Stage 14a: the renamed profile has no alias; `ibm_kyiv` is just a name without a file
#guard profilePath "ibm_kyiv" == "profiles/ibm_kyiv.json"
#guard profilePath "my/kyiv.json" == "my/kyiv.json"

/-- The Grover hardware check against `p` (G = 390, δ = 7/128). -/
def groverHw : Option HardwareCheck := (readProfile (profileText "200" "\"0.01\"")).toOption.map
  fun p => HardwareCheck.of p "h" ⟨15, 230, 72, 7⟩ (7 / 128) 390

#guard groverHw.map (hardwareJson · |>.compress) == some
  ("{\"G\":390,\"components\":{\"a\":{\"budget\":127,\"fits\":true,\"required\":7},\
    \"d\":{\"budget\":200,\"fits\":false,\"required\":230},\
    \"t\":{\"budget\":null,\"fits\":true,\"required\":72},\
    \"w\":{\"budget\":127,\"fits\":true,\"required\":15}},\"delta_hw\":\"2531/640\",\
    \"fits\":false,\"note\":\"" ++ hardwareNote ++ "\",\"p_bar\":\"1/100\",\"profile\":\"p\",\
    \"profile_hash\":\"h\",\"vacuous\":true}")

/-! ## Axioms of the lemmas a certificate instantiates (§9.5.1) -/

/-- info: 'CQRV.Certify.sin_sq_odd_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin_sq_odd_mul

/-- info: 'CQRV.Certify.grover_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grover_certificate

/-- info: 'CQRV.Synthesis.Network.countSat_eq_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Network.countSat_eq_card

/-- info: 'CQRV.Grover.grover_parametric_lemma_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CQRV.Grover.grover_parametric_lemma_gen

/-- info: 'CQRV.Certify.grover_certificate_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grover_certificate_coherent

/--
info: 'CQRV.Certify.grover_certificate_few' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms grover_certificate_few

/--
info: 'CQRV.Certify.grover_certificate_few_all' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms grover_certificate_few_all

/-! ## Stage 17a — the gate literal of the phase gates (no synthesized circuit contains them) -/

#guard gateLit (.p (-3) 5 (.data 0)) == ".p (-3) 5 (.data 0)" &&
  gateLit (.cp 1 2 (.data 0) (.anc 1)) == ".cp 1 2 (.data 0) (.anc 1)" &&
  gateLit (.ifBit 0 (.cp 1 1 (.data 0) (.data 1))) == ".ifBit 0 (.cp 1 1 (.data 0) (.data 1))"

end CQRV.Tests.Certify
