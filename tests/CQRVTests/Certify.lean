module

import CQRV.Certify.Basic
import CQRV.Emit.Basic
meta import CQRV.Certify.Basic
meta import CQRV.Emit.Basic

/-!
# Tests for `CQRV.Certify` and `CQRV.Emit` (Stage 8a; report §8.4.2–8.4.4, §9.5.3, §5.3)

SHA3-256 on the reviewer's vectors (the 200-string differential against hashlib is
`tests/diff/sha3_diff.py`), the exact δ, the sample certificate of grover_pred_037 (no kernel
check: `status` "not yet audited"; the schema check is `tests/diff/cert_schema.py`) and the shape
of the emitted QIR / QASM (the re-parse is `tests/diff/emit_diff.py`).
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
  | .ok c => c.delta == 7 / 128 && c.grade == ⟨15, 230, 72, 7⟩ && c.status == .notYetAudited &&
      c.n == 8 && c.M == 32 && c.r == 2 && c.proofHash.isNone && c.axioms.isEmpty
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

end CQRV.Tests.Certify
