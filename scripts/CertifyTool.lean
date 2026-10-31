import CQRV.Certify.Basic

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
-/

open CQRV.Certify

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
  | _ => IO.eprintln "usage: CertifyTool (sha3 | sample <file.cqr> | audit <Cert.lean> <theorem> \
      [<theorem> …])"
         return 2
