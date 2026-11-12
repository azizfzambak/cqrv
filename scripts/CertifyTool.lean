import CQRV.Certify.Basic
import CQRV.Emit.Basic
import CQRV.Synthesis.Counting
import CQRV.Circuit.GradeCompose

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
* `qft-sample <m> [<kmax>] [--adjoint]` (Stage 18b B4, PHASE2_SPEC.md §A.2): the IR JSON of
  `qftCircuit m` (or `aqftCircuit m kmax`), with `--adjoint` the inverse circuit
  (`adjointGates`); `qft-sample --all <m-max>` prints one JSON object
  `{"m": {"qft", "adjoint", "aqft": {"kmax": …}}}` for `m = 1 .. m-max`, which is what
  `tests/diff/qft_diff.py` reads (one Lean start for the whole run).
* `counting-sample <file.cqr> <m> [--kmax k] [--shape tree|chain] [--uncompute mbu|coherent]
  [--lean <out.lean>]` (Stage 19b B5, PHASE2_SPEC.md §A.3): one JSON object for the counting
  circuit of the predicate of `file.cqr` with `m` phase qubits — the circuit (`Circuit.toJson`),
  the block table (every **distinct** block once: name, first gate, length, multiplicity, bits,
  ancillae, `liveEnd`, T-count, grade, `GradeExt`, its own IR JSON), the measured grade and
  `GradeExt` of the whole, and the composed bound of Stage 19a (`⊕` with the multiplicities;
  `tDepth` as `tDepth(init) + Σ tCount`), plus the predicate's truth table (character `x` = the
  value on input `x`, bit `k` of `x` = input bit `k`). `--lean` also writes the Stage 19b B6 probe
  file: the distinct blocks as literals with their `… = .ok block` link and `grade_eq` /
  `gradeExt_eq` by `decide +kernel` (report only, not a certificate). `counting-sample --all
  <m-max> <file.cqr>…` prints `{"<file name>": {"name", "n", "m": {"<m>": {"mbu", "coherent",
  "aqft": {"<kmax>": …}}}}}` for `m = 1 .. m-max` (the AQFT variants in mode `coherent`,
  `kmax = 1 .. m − 1`), which `tests/diff/counting_diff.py` reads (one Lean start).
* `count-certify <file.cqr> <m> --out <dir> [--report]` (Stage 20b3, PHASE2_SPEC.md §A.4
  "Amendments before Stage 20b3"): the counting certificate of the predicate of `file.cqr` with
  `m` phase qubits (exact inverse QFT, shape tree, mode MBU; `M` by `Network.countSat`): writes
  `Cert.lean` (`CQRV.Certify.renderCountCert`, the compositional form), kernel-checks it and
  audits `cert` and `cert_count` (`checkAndAudit`), then writes `certificate.json`
  (`CountCertificate.toJson`, schema 1.10.0, pattern `Count`), `<name>.qir`, `<name>.qasm` and,
  with `--report`, `run_report.{md,json}`; on a failed check it writes no JSON and exits 1, as
  `cqr certify` does. Stage 21 wires the same functions to `cqr certify --problem count`.
* `command-output <timeout-ms> <cmd> <args…>` (Stage 18b B0): run `CQRV.Certify.runCommand` —
  the guarded command runner of the machine detection — and print its trimmed stdout, or `none`
  (`none (timed out after T ms)` when the child was killed at the timeout), then `wall_ms: N`.
  `tests/diff/certify_check.py` calls it on a child that sleeps past a 1 s timeout (asserting
  `none` within 5 s and that the child is gone) and on one that exits at once.
-/

open CQRV CQRV.Synthesis CQRV.Certify

/-! ## Stage 19b B5 / B6 — `counting-sample` -/

structure CountingOpts where
  pos : List String := []
  all : Bool := false
  kmax : Option Nat := none
  shape : DiffusionShape := .tree
  mode : UncomputeMode := .mbu
  lean : Option String := none

def parseCountingOpts : List String → CountingOpts → Option CountingOpts
  | [], o => some o
  | "--all" :: xs, o => parseCountingOpts xs { o with all := true }
  | "--kmax" :: k :: xs, o => k.toNat?.bind fun k => parseCountingOpts xs { o with kmax := some k }
  | "--shape" :: "tree" :: xs, o => parseCountingOpts xs { o with shape := .tree }
  | "--shape" :: "chain" :: xs, o => parseCountingOpts xs { o with shape := .chain }
  | "--uncompute" :: "mbu" :: xs, o => parseCountingOpts xs { o with mode := .mbu }
  | "--uncompute" :: "coherent" :: xs, o => parseCountingOpts xs { o with mode := .coherent }
  | "--lean" :: f :: xs, o => parseCountingOpts xs { o with lean := some f }
  | x :: xs, o =>
    if x.startsWith "--" then none else parseCountingOpts xs { o with pos := o.pos ++ [x] }

def shapeStr : DiffusionShape → String
  | .tree => "tree"
  | .chain => "chain"

def modeStr : UncomputeMode → String
  | .mbu => "mbu"
  | .coherent => "coherent"

def gradeJ (g : Grade) : Lean.Json :=
  Lean.Json.mkObj [("w", Lean.toJson g.w), ("d", Lean.toJson g.d), ("t", Lean.toJson g.t),
    ("a", Lean.toJson g.a)]

def gradeExtJ (g : GradeExt) : Lean.Json :=
  Lean.Json.mkObj [("two_qubit", Lean.toJson g.twoQ), ("t_depth", Lean.toJson g.tDepth),
    ("rot", Lean.toJson g.rot), ("meas", Lean.toJson g.meas), ("ff", Lean.toJson g.ff)]

/-- The distinct blocks of `countingCircuit` in program order: name, the block, its multiplicity
and (for a controlled iterate) its phase qubit. -/
def countingBlocks (N : Network) (n m : Nat) (kmax : Option Nat) (shape : DiffusionShape)
    (mode : UncomputeMode) : Except DSL.Diagnostic (List (String × Circuit × Nat × Option Nat)) := do
  let cgs ← (List.range m).mapM fun j => controlledGrover N n m j shape mode
  return [("h_layer", countingHLayer n m, 1, none)] ++
    (cgs.zipIdx.map fun (b, j) => (s!"cg_{j}", b, 2 ^ j, some j)) ++
    [("inverse", countingInverse n m kmax, 1, none)]

/-- The composed bound of Stage 19a: `init ⊕ Σ mult • block` (`grade_foldl_append_le`,
`grade_replicate_le`). -/
def composedGrade : List (String × Circuit × Nat × Option Nat) → Grade
  | [] => ⟨0, 0, 0, 0⟩
  | (_, b, _, _) :: rest => rest.foldl (fun g (_, c, mult, _) => g + mult • c.grade) b.grade

/-- The composed `GradeExt`: the sums (`gradeExt_*_foldl_append`) and the T-depth bound
`tDepth(init) + Σ mult · tCount` (`gradeExt_tDepth_foldl_append_le`). -/
def composedGradeExt : List (String × Circuit × Nat × Option Nat) → GradeExt
  | [] => ⟨0, 0, 0, 0, 0⟩
  | (_, b, _, _) :: rest => rest.foldl (fun g (_, c, mult, _) =>
      ⟨g.twoQ + mult * c.gradeExt.twoQ, g.tDepth + mult * c.tCount, g.rot + mult * c.gradeExt.rot,
       g.meas + mult * c.gradeExt.meas, g.ff + mult * c.gradeExt.ff⟩) b.gradeExt

def blockRow (nm : String) (b : Circuit) (mult first : Nat) : Lean.Json :=
  Lean.Json.mkObj [("name", Lean.toJson nm), ("first", Lean.toJson first),
    ("length", Lean.toJson b.gates.length), ("multiplicity", Lean.toJson mult),
    ("n_bits", Lean.toJson b.nBits), ("n_anc", Lean.toJson b.nAnc),
    ("live_end", Lean.toJson b.liveEnd), ("t_count", Lean.toJson b.tCount),
    ("grade", gradeJ b.grade), ("grade_ext", gradeExtJ b.gradeExt), ("circuit", b.toJson)]

/-- The `counting-sample` JSON object. -/
def countingSampleJson (name : String) (N : Network) (n m : Nat) (kmax : Option Nat)
    (shape : DiffusionShape) (mode : UncomputeMode) : Except DSL.Diagnostic Lean.Json := do
  let C ← countingCircuit N n m kmax shape mode
  let tbl ← countingBlocks N n m kmax shape mode
  let rows := (tbl.foldl (fun (acc, pos) (nm, b, mult, _) =>
    (acc ++ [blockRow nm b mult pos], pos + mult * b.gates.length)) (([] : List Lean.Json), 0)).1
  return Lean.Json.mkObj [("name", Lean.toJson name), ("n", Lean.toJson n), ("m", Lean.toJson m),
    ("kmax", match kmax with | some k => Lean.toJson k | none => Lean.Json.null),
    ("shape", Lean.toJson (shapeStr shape)), ("uncompute", Lean.toJson (modeStr mode)),
    ("truth_table", Lean.toJson (truthTable n (N.pred n))), ("circuit", C.toJson),
    ("blocks", Lean.Json.arr rows.toArray),
    ("measured", Lean.Json.mkObj [("gates", Lean.toJson C.gates.length),
      ("n_anc", Lean.toJson C.nAnc), ("n_bits", Lean.toJson C.nBits),
      ("live_end", Lean.toJson C.liveEnd), ("grade", gradeJ C.grade),
      ("grade_ext", gradeExtJ C.gradeExt)]),
    ("composed", Lean.Json.mkObj [("grade", gradeJ (composedGrade tbl)),
      ("grade_ext", gradeExtJ (composedGradeExt tbl))])]

/-- The Stage 19b B6 probe file: every distinct block as a literal with its link to the builder
and its exact `grade_eq` / `gradeExt_eq` by `decide +kernel` (as `emitted_ok` / `grade_eq` of a
certificate; report only). Every declaration starts at column 0 (the per-declaration profiler of
`scripts/kernel_forms.py` inserts its markers before top-level `theorem` / `def` lines). -/
def countingBlocksLean (name file : String) (N : Network) (n m : Nat) (kmax : Option Nat)
    (shape : DiffusionShape) (mode : UncomputeMode) : Except DSL.Diagnostic String := do
  let C ← countingCircuit N n m kmax shape mode
  let tbl ← countingBlocks N n m kmax shape mode
  let kmaxLit := match kmax with | some k => s!"(some {k})" | none => "none"
  let decl (nm : String) (b : Circuit) (mult : Nat) (j : Option Nat) : List String :=
    let g := b.grade
    let e := b.gradeExt
    let link := match j with
      | some j => [s!"theorem {nm}_ok : controlledGrover net {n} {m} {j} .{shapeStr shape} \
          .{modeStr mode} = .ok {nm} :=", "  except_ok_of_check _ _ (by decide +kernel)"]
      | none =>
        if nm == "h_layer" then
          [s!"theorem {nm}_ok : countingHLayer {n} {m} = {nm} := by decide +kernel"]
        else [s!"theorem {nm}_ok : countingInverse {n} {m} {kmaxLit} = {nm} := by decide +kernel"]
    [s!"/-- Block `{nm}`: {b.gates.length} gates, multiplicity {mult}, `liveEnd` {b.liveEnd}. -/",
     s!"def {nm} : Circuit := {circuitLit b}", "",
     "/-- The link to the builder (as `emitted_ok`). -/"] ++ link ++ ["",
     s!"/-- The measured grade of `{nm}` (as `grade_eq`). -/",
     s!"theorem {nm}_grade_eq : Synthesis.grade {nm} = ⟨{g.w}, {g.d}, {g.t}, {g.a}⟩ := \
       by decide +kernel", "",
     s!"/-- The measured `GradeExt` of `{nm}` (as `gradeExt_eq`). -/",
     s!"theorem {nm}_gradeExt_eq : Synthesis.gradeExt {nm} = \
       ⟨{e.twoQ}, {e.tDepth}, {e.rot}, {e.meas}, {e.ff}⟩ := by decide +kernel", ""]
  let gc := composedGrade tbl
  let gm := C.grade
  let ec := composedGradeExt tbl
  let em := C.gradeExt
  let header : List String := [
    "import CQRV", "",
    "/-! Stage 19b B6 probe (docs/tasks/STAGE19_TASK.md; PHASE2_SPEC.md §A.3, the compositional",
    s!"certificate form): the distinct blocks of `countingCircuit` for `{name}` ({file}),",
    s!"n = {n}, m = {m}, shape {shapeStr shape}, uncomputation mode {modeStr mode}, each as a \
      literal with its",
    "`… = .ok block` link and its exact `grade_eq` / `gradeExt_eq` by `decide +kernel`. Generated by",
    "`scripts/CertifyTool.lean counting-sample … --lean`; measured per declaration by",
    "`scripts/counting_blocks.sh` (docs/benchmarks/COUNTING_BLOCKS.md). Report only: not a certificate.",
    s!"The whole circuit has {C.gates.length} gates; measured grade (compiled evaluation) \
      ({gm.w}, {gm.d}, {gm.t}, {gm.a}),",
    s!"composed bound ({gc.w}, {gc.d}, {gc.t}, {gc.a}); measured `GradeExt` \
      ({em.twoQ}, {em.tDepth}, {em.rot}, {em.meas}, {em.ff}),",
    s!"composed ({ec.twoQ}, {ec.tDepth}, {ec.rot}, {ec.meas}, {ec.ff}). -/", "",
    s!"namespace CQRV.CountingBlocks.«{name}_{modeStr mode}»", "",
    "open CQRV CQRV.Synthesis CQRV.Certify", "",
    s!"/-- The Boolean network of `{name}` (`toNetwork`, §6.1.2). -/",
    s!"def net : Network := {networkLit N}", ""]
  let body := tbl.flatMap fun (nm, b, mult, j) => decl nm b mult j
  return "\n".intercalate (header ++ body ++
    [s!"end CQRV.CountingBlocks.«{name}_{modeStr mode}»", ""])

/-- Parse, check and translate a `.cqr` file: its name, arity and (well-formed) network. -/
def readNetwork (file : String) : IO (Except DSL.Diagnostic (String × Nat × Network)) := do
  let src ← IO.FS.readFile file
  return do
    let tp ← CQRV.DSL.parse src >>= CQRV.DSL.check
    let net ← toNetwork tp
    if !net.wf then
      throw (DSL.Diagnostic.at .synthesis .unsupportedNetwork ⟨1, 1⟩
        s!"the network of {tp.name} is not well formed")
    return (tp.name, tp.arity, net)

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
  | "qft-sample" :: rest =>
    -- Stage 18b B4 (PHASE2_SPEC.md §A.2): the IR JSON of `qftCircuit m` / `aqftCircuit m kmax`,
    -- `--adjoint` for the inverse (`adjointGates`), `--all <m-max>` for every circuit the harness
    -- needs in one JSON object (one Lean start instead of one per circuit).
    let usage : IO UInt32 := do
      IO.eprintln "usage: CertifyTool qft-sample (<m> [<kmax>] [--adjoint] | --all <m-max>)"
      return 2
    let adj := rest.contains "--adjoint"
    let circuitOf (m : Nat) (kmax : Option Nat) : CQRV.Circuit :=
      let c := match kmax with | some k => aqftCircuit m k | none => qftCircuit m
      if adj then ⟨c.nData, adjointGates c.gates⟩ else c
    match rest.filter (· != "--adjoint") with
    | ["--all", s] =>
      match s.toNat? with
      | some mMax =>
        let entries := (List.range mMax).map fun i =>
          let m := i + 1
          (toString m, Lean.Json.mkObj
            [("qft", (qftCircuit m).toJson),
             ("adjoint", (⟨m, adjointGates (qftGates m)⟩ : CQRV.Circuit).toJson),
             ("aqft", Lean.Json.mkObj ((List.range m).map fun k =>
               (toString (k + 1), (aqftCircuit m (k + 1)).toJson)))])
        IO.println (Lean.Json.mkObj entries).compress
        return 0
      | none => usage
    | [mStr] =>
      match mStr.toNat? with
      | some m => IO.println (circuitOf m none).toJson.compress; return 0
      | none => usage
    | [mStr, kStr] =>
      match mStr.toNat?, kStr.toNat? with
      | some m, some k => IO.println (circuitOf m (some k)).toJson.compress; return 0
      | _, _ => usage
    | _ => usage
  | "counting-sample" :: rest =>
    -- Stage 19b B5 / B6 (PHASE2_SPEC.md §A.3): the counting circuit of a predicate with its
    -- block table, measured grade and composed bound; `--all` for the harness; `--lean` for
    -- the B6 probe file.
    let usage : IO UInt32 := do
      IO.eprintln "usage: CertifyTool counting-sample (<file.cqr> <m> [--kmax k] [--shape tree|chain] \
        [--uncompute mbu|coherent] [--lean <out.lean>] | --all <m-max> <file.cqr>…)"
      return 2
    let some o := parseCountingOpts rest {} | usage
    if o.all then
      match o.pos with
      | mStr :: files =>
        let some mMax := mStr.toNat? | usage
        if files.isEmpty then usage else
        let mut entries : List (String × Lean.Json) := []
        for file in files do
          match ← readNetwork file with
          | .error d => IO.println d.toJson.compress; return 1
          | .ok (name, n, net) =>
            let perM : Except DSL.Diagnostic (List (String × Lean.Json)) :=
              (List.range mMax).mapM fun i => do
                let m := i + 1
                let mbu ← countingSampleJson name net n m none o.shape .mbu
                let coh ← countingSampleJson name net n m none o.shape .coherent
                let aq ← (List.range (m - 1)).mapM fun k => do
                  let j ← countingSampleJson name net n m (some (k + 1)) o.shape .coherent
                  return (toString (k + 1), j)
                return (toString m, Lean.Json.mkObj [("mbu", mbu), ("coherent", coh),
                  ("aqft", Lean.Json.mkObj aq)])
            match perM with
            | .error d => IO.println d.toJson.compress; return 1
            | .ok ms =>
              let key := (System.FilePath.mk file).fileName.getD file
              entries := entries ++ [(key, Lean.Json.mkObj [("name", Lean.toJson name),
                ("n", Lean.toJson n), ("m", Lean.Json.mkObj ms)])]
        IO.println (Lean.Json.mkObj entries).compress
        return 0
      | _ => usage
    else
      match o.pos with
      | [file, mStr] =>
        let some m := mStr.toNat? | usage
        match ← readNetwork file with
        | .error d => IO.println d.toJson.compress; return 1
        | .ok (name, n, net) =>
          match countingSampleJson name net n m o.kmax o.shape o.mode with
          | .error d => IO.println d.toJson.compress; return 1
          | .ok j =>
            if let some out := o.lean then
              match countingBlocksLean name file net n m o.kmax o.shape o.mode with
              | .error d => IO.println d.toJson.compress; return 1
              | .ok text => IO.FS.writeFile out text
            IO.println j.compress
            return 0
      | _ => usage
  | "count-certify" :: rest =>
    -- Stage 20b3 (PHASE2_SPEC.md §A.4 "Amendments before Stage 20b3"): the counting certificate
    let usage : IO UInt32 := do
      IO.eprintln "usage: CertifyTool count-certify <file.cqr> <m> --out <dir> [--report]"
      return 2
    let rec parse : List String → Option (List String × Option String × Bool)
      | [] => some ([], none, false)
      | "--out" :: d :: xs => (parse xs).map fun (p, _, r) => (p, some d, r)
      | "--report" :: xs => (parse xs).map fun (p, o, _) => (p, o, true)
      | x :: xs => if x.startsWith "--" then none else (parse xs).map fun (p, o, r) => (x :: p, o, r)
    let some (pos, out, report) := parse rest | usage
    let [file, mStr] := pos | usage
    let some m := mStr.toNat? | usage
    let some dir0 := out | usage
    let src ← IO.FS.readFile file
    let tp ← match (CQRV.DSL.parse src >>= CQRV.DSL.check) with
      | .error d => IO.println d.toJson.compress; return 1
      | .ok tp => pure tp
    let net ← match toNetwork tp with
      | .error d => IO.println d.toJson.compress; return 1
      | .ok net => pure net
    if !net.wf then
      IO.eprintln s!"count-certify: the network of {tp.name} is not well formed"; return 1
    let n := tp.arity
    let q ← match CountRequest.ofProgram tp src net n m with
      | .error e => IO.eprintln s!"count-certify: {e}"; return 1
      | .ok q => pure q
    let cfg ← match RefConfig.ofFiles (← IO.FS.readFile "lean-toolchain")
        (← IO.FS.readFile "lake-manifest.json") with
      | .ok c => pure c
      | .error e => IO.eprintln s!"count-certify: {e}"; return 2
    let text := renderCountCert q
    let qirText ← match CQRV.Emit.emitQIR tp.name q.circuit with
      | .ok t => pure t
      | .error d => IO.println d.toJson.compress; return 1
    let dir := dir0.dropEndWhile (fun c => c == '/' || c == '\\')
    let fileOf (nm : String) : String := s!"{dir}/{nm}"
    IO.FS.createDirAll dir.toString
    let certPath := fileOf "Cert.lean"
    IO.FS.writeFile certPath text
    -- kernel check and audit of `cert` and `cert_count` (one Lean run)
    let o ← match ← checkAndAudit certPath q.theoremName with
      | .ok o => pure o
      | .error e => IO.eprintln s!"count-certify: {certPath}: {e}"; return 1
    let some axsCount := parseAxioms q.countTheoremName o.check.output
      | IO.eprintln s!"count-certify: no `#print axioms {q.countTheoremName}` line"; return 1
    let bad := (match o.result with | .pass => [] | .fail b => b) ++
      (match auditAxioms axsCount with | .pass => [] | .fail b => b)
    let obligations := (if bad.contains "sorryAx" then ["sorryAx"] else []) ++
      (bad.filter (· != "sorryAx")).eraseDups
    let status := if bad.isEmpty then Status.certified else Status.withObligations
    let timing : KernelTiming :=
      { wallMs := o.check.wallMs, kernelMs := o.check.kernelMs, runs := 1,
        statistic := "single run" }
    let mi ← detectMachine
    for c in mi.timedOut do
      IO.eprintln s!"count-certify: machine detection: `{c}` timed out after \
        {machineCommandTimeoutMs / 1000} s; machine fields from the environment"
    let cfg := { cfg with cpu := some (mi.cpu.getD "unknown"), logicalCpus := mi.logicalCpus,
                          clock := mi.clock, leanThreads := ← IO.getEnv "LEAN_NUM_THREADS",
                          kernelCheck := timing }
    let axioms := (o.axioms ++ axsCount).eraseDups
    let cert := { CountCertificate.ofRequest q cfg with
      proofHash := some (proofHash text cfg.lean cfg.mathlib cfg.physlib), axioms, status,
      theoremName := some q.theoremName, obligations }
    IO.FS.writeFile (fileOf "certificate.json") (cert.toJson.compress ++ "\n")
    IO.FS.writeFile (fileOf s!"{tp.name}.qir") qirText
    IO.FS.writeFile (fileOf s!"{tp.name}.qasm") (CQRV.Emit.emitQASM tp.name q.circuit)
    let eps := round6 (aeEpsFloat n q.M m)
    let statusLine := match status with
      | .certified => s!"certified (ε ≈ {eps}, δ = 1 − 8/π² ≈ {round6 aeDeltaFloat}; universal in \
          M ≥ 1; M = {q.M} decided by the kernel)"
      | _ => s!"certificate with tracked obligations: {", ".intercalate obligations}"
    if report then
      let rd : CountRunData :=
        { q, source := file, certPath, timing, axioms, statusLine,
          certified := status == .certified }
      IO.FS.writeFile (fileOf "run_report.md") rd.toMarkdown
      IO.FS.writeFile (fileOf "run_report.json") (rd.toJson.pretty ++ "\n")
    let kms := match timing.kernelMs with | some k => s!", {msText k} kernel" | none => ""
    IO.println s!"kernel check: {certPath} (exit 0, {msText timing.wallMs} wall{kms}; \
      {timing.statistic})"
    IO.println s!"axioms: {", ".intercalate axioms}"
    IO.println s!"wrote: {fileOf "certificate.json"}, {fileOf s!"{tp.name}.qir"}, \
      {fileOf s!"{tp.name}.qasm"}{if report then s!", {fileOf "run_report.md"}, \
      {fileOf "run_report.json"}" else ""}"
    IO.println statusLine
    return 0
  | "command-output" :: timeoutStr :: cmd :: cmdArgs =>
    -- Stage 18b B0: exercise `runCommand` (the timeout of the machine-detection commands)
    let some timeoutMs := timeoutStr.toNat?
      | IO.eprintln "usage: CertifyTool command-output <timeout-ms> <cmd> <args…>"; return 2
    let t0 ← IO.monoMsNow
    let r ← runCommand cmd cmdArgs.toArray timeoutMs
    let t1 ← IO.monoMsNow
    match r with
    | .ok s => IO.println s
    | .failed => IO.println "none"
    | .timedOut => IO.println s!"none (timed out after {timeoutMs} ms)"
    IO.println s!"wall_ms: {t1 - t0}"
    return 0
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
      <out.lean> | qft-sample (<m> [<kmax>] [--adjoint] | --all <m-max>) | counting-sample \
      (<file.cqr> <m> [--kmax k] [--shape tree|chain] [--uncompute mbu|coherent] [--lean <out.lean>] \
      | --all <m-max> <file.cqr>…) | count-certify <file.cqr> <m> --out <dir> [--report] | \
      command-output <timeout-ms> <cmd> <args…>)"
         return 2
