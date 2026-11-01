import CQRV.Certify.Basic
import CQRV.Emit.Basic

/-!
# Test helper for the Stage 8a / 8b checks (report §8.4.2, §9.5.1, §9.5.3)

Run with `lake env lean --run scripts/CertifyTool.lean <command>` (after `lake build`); used by
`tests/diff/sha3_diff.py` and `tests/diff/cert_schema.py` (driver `scripts/check_emit.sh`).

* `sha3`: read lines of hex-encoded byte strings from stdin (an empty line is the empty string)
  and print the SHA3-256 of each (`CQRV.Certify.SHA3.sha3_256Hex`), one per line.
* `sample <file.cqr>`: print the Stage 8a certificate JSON of a source file (compact, keys
  sorted): no kernel check, no axiom audit, `status` "not yet audited"; the reference
  configuration is read from `lean-toolchain` and `lake-manifest.json`.
* `audit <Cert.lean> <theorem> [<theorem> …]` (Stage 8b; several theorems since Stage 16b):
  kernel-check a certificate file once (`lake env lean`) and audit the axioms of each
  `#print axioms <theorem>` line (`CQRV.Certify.checkAndAudit`, `parseAxioms`); exit 0 if every
  audit passes, 3 if one fails (the offending axioms are printed), 1 if Lean fails or a line is
  missing. Used by `scripts/print_axioms.sh` (blocking; `cert` and `front_end` of every committed
  certificate) and by the injected-`sorry` test of `scripts/check_certify.sh`.
* `emit-sample <json|qasm|qir> [--decompose-cp] [--if-cp]` (Stage 17b, PHASE2_SPEC.md §A.1): the
  sample circuit `CQRV.Emit.sampleCircuit` (every gate constructor, the phase gates included) as
  IR JSON (through `Circuit.decomposeCp` with `--decompose-cp`), OpenQASM 3 or QIR; `--if-cp`
  takes `sampleCircuitIfCp` instead (one `ifBit` over `cp 1 1`): `qir --if-cp` prints the
  diagnostic JSON `unsupported_in_qir` and exits 1. The test path for gates no synthesized circuit
  contains (`tests/diff/emit_diff.py`).
* `front-end <file.cqr> <out.lean>` (Stage 18a A0, docs/tasks/STAGE18_TASK.md): write a standalone
  Lean file holding exactly the front-end block of a certificate for any typed program — `net`
  (the network literal) and `CertRequest.progBlock` (`prog`, `prog_scoped`, `net_ok`,
  `front_end`) — without the Grover match (the extractor classifies a program with a second
  parameter, such as `k : Nat 3`, as a decision problem, so `cqr certify` cannot produce its
  certificate). `scripts/kernel_forms.py` profiles that file to name the slow declaration of the
  `Nat m` item (report only; no fix).
-/

open CQRV CQRV.Synthesis CQRV.Certify

/-- Decode a hex string (even length, `0-9a-f`). -/
def unhex (s : String) : Option ByteArray := do
  let nib (c : Char) : Option UInt8 :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8 else none
  let cs := s.toList
  if cs.length % 2 != 0 then none
  let mut out := ByteArray.empty
  for i in [0:cs.length / 2] do
    out := out.push ((← nib cs[2 * i]!) * 16 + (← nib cs[2 * i + 1]!))
  return out

def main (args : List String) : IO UInt32 := do
  match args with
  | ["sha3"] =>
    let stdin ← IO.getStdin
    let mut line ← stdin.getLine
    while !line.isEmpty do
      match unhex line.trimAscii.toString with
      | some b => IO.println (SHA3.sha3_256Hex b)
      | none => IO.eprintln s!"bad hex line: {line}"; return 1
      line ← stdin.getLine
    return 0
  | ["sample", file] =>
    let cfg ← RefConfig.ofFiles (← IO.FS.readFile "lean-toolchain")
      (← IO.FS.readFile "lake-manifest.json") |> IO.ofExcept
    match certificateOf (← IO.FS.readFile file) cfg with
    | .ok c => IO.println c.toJson.compress; return 0
    | .error e => IO.eprintln e; return 1
  | "audit" :: file :: thm :: more =>
    match ← checkAndAudit file thm with
    | .error e => IO.eprintln s!"audit {file}: {e}"; return 1
    | .ok o =>
      -- Stage 16b: further theorems of the same file are audited from the same Lean run
      let mut results : List (String × List String × AuditResult) := [(thm, o.axioms, o.result)]
      for t in more do
        match parseAxioms t o.check.output with
        | none => IO.eprintln s!"audit {file}: no `#print axioms {t}` line in the Lean output"; return 1
        | some axs => results := results ++ [(t, axs, auditAxioms axs)]
      let mut bad : List String := []
      for (t, axs, r) in results do
        IO.println s!"{t}: {", ".intercalate axs}"
        if let .fail b := r then bad := bad ++ b
      if bad.isEmpty then
        IO.println s!"axiom audit: {file}: pass"; return 0
      else
        IO.println s!"axiom audit: {file}: FAILED ({", ".intercalate bad})"
        return 3
  | "emit-sample" :: fmt :: flags =>
    if !flags.all (fun f => f == "--decompose-cp" || f == "--if-cp") then
      IO.eprintln "usage: CertifyTool emit-sample <json|qasm|qir> [--decompose-cp] [--if-cp]"
      return 2
    let ifCp := flags.contains "--if-cp"
    let C := if ifCp then CQRV.Emit.sampleCircuitIfCp else CQRV.Emit.sampleCircuit
    let name := if ifCp then "sample_if_cp" else "sample"
    match fmt with
    | "json" =>
      let C' : CQRV.Circuit :=
        if flags.contains "--decompose-cp" then ⟨C.nData, CQRV.Circuit.decomposeCp C.gates⟩ else C
      IO.println C'.toJson.compress
      return 0
    | "qasm" => IO.print (CQRV.Emit.emitQASM name C); return 0
    | "qir" =>
      match CQRV.Emit.emitQIR name C with
      | .ok text => IO.print text; return 0
      | .error d => IO.println d.toJson.compress; return 1
    | _ =>
      IO.eprintln "usage: CertifyTool emit-sample <json|qasm|qir> [--decompose-cp] [--if-cp]"
      return 2
  | ["front-end", file, out] =>
    let src ← IO.FS.readFile file
    match (CQRV.DSL.parse src >>= CQRV.DSL.check) with
    | .error d => IO.println d.toJson.compress; return 1
    | .ok tp =>
      match toNetwork tp with
      | .error d => IO.println d.toJson.compress; return 1
      | .ok net =>
        let n := tp.arity
        -- a request with the front-end fields only (the rest is unused by `progBlock`)
        let q : CertRequest :=
          { name := tp.name, net, prog := tp, n, M := 0, r := 0, circuit := ⟨n, []⟩, delta := 0,
            grade := ⟨0, 0, 0, 0⟩, gradeExt := ⟨0, 0, 0, 0, 0⟩, nAnc := 0, predicateHash := "" }
        let text := s!"import CQRV

/-! Stage 18a A0 probe (docs/tasks/STAGE18_TASK.md): the front-end block of a certificate for
`{tp.name}` ({file}), as `cqr certify` would write it, without the rest of the certificate. -/

namespace CQRV.Forms.«{tp.name}»

open CQRV CQRV.Synthesis CQRV.Grover CQRV.Certify

/-- The Boolean network of the request (`toNetwork`, §6.1.2). -/
def net : Network := {networkLit net}

{q.progBlock}
end CQRV.Forms.«{tp.name}»
"
        IO.FS.writeFile out text
        IO.println s!"wrote {out} (n = {n}, {net.nodes.size} nodes)"
        return 0
  | _ => IO.eprintln "usage: CertifyTool (sha3 | sample <file.cqr> | audit <Cert.lean> <theorem> \
      [<theorem> …] | emit-sample <json|qasm|qir> [--decompose-cp] [--if-cp] | front-end <file.cqr> \
      <out.lean>)"
         return 2
