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
      c.n == 8 && c.M == 32 && c.r == 2 && c.proofHash.isNone && c.axioms.isEmpty
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

def qir : String := emitQIR "grover_pred_037" groverC

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
    | .ok gi => some (CertRequest.ofInstance tp.name groverSrc gi 32)
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
-- Stage 9a: an XOR network gets the same proved certificate as an AND/NOT/OR network (oracle
-- certificate, no `sorry`, no `xorFree` side condition)
#guard groverReq.all fun q => ((renderCert { q with net := xorNet }).splitOn "sorry").length == 1
#guard groverReq.all fun q =>
  ((renderCert { q with net := xorNet }).splitOn "def oracle : OracleCert 8 where").length == 2
#guard (groverCert.splitOn "hXor").length == 1

/-! ## `symDiff` by structural insertion sort (kernel-evaluable, Stage 8b) -/

#guard symDiff [.anc 2, .data 1, .data 0] [.data 1, .anc 0] == [.data 0, .anc 0, .anc 2]
#guard symDiff [] [.anc 1, .data 3, .anc 0] == [.data 3, .anc 0, .anc 1]
example : symDiff [.anc 1, .data 0] [.data 2] = [.data 0, .data 2, .anc 1] := by decide +kernel

/-! ## Hardware profiles (Stage 11b, §3.3.2–3.3.3)

`profileOfJson` on inline profile texts (the file `profiles/ibm_kyiv.json` itself is read by
`tests/diff/certify_check.py` through `cqr certify --profile ibm_kyiv`). -/

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

end CQRV.Tests.Certify
