import CQRV.DSL.Basic
import CQRV.Matching.Basic
import CQRV.Synthesis.Basic
import CQRV.Certify.Basic
import CQRV.Emit.Basic

/-!
# `cqr` command-line interface

Report §9.1 (Phase I), CLAUDE.md layout `Apps/cqr/`. Stage 3 implements `check` and `extract`
(report §4.2.2, §7.2), Stage 4 `match` (report §4.2.4, §4.3.2), Stage 5 `synthesize` (report
§6.1–6.2); the other subcommands exit with code 2 and name their stage.

* `cqr check <file>` — parse + surface check; exit 0, or print the diagnostic JSON and exit 1.
* `cqr check <file> --truth-table` — Stage 9b: also print `{name, n, evaluator, network}` with
  the truth tables of the DSL evaluator (`evalProgram`) and of `Network.pred (toNetwork …)` as
  `0`/`1` strings (character `x` = value on input `x`, bit `k` of `x` = input bit `k`), for
  `n ≤ 16`; the differential harness compares them with its own reference evaluator.
* `cqr extract <file> [--solutions M]` — print the `SigmaIn` JSON (exit 0), or the diagnostic
  JSON (exit 1). `--solutions M` supplies the ground solution count when ℰ cannot compute it
  (DECISIONS.md 2026-10-23, decision 5); a value that contradicts ℰ's is a diagnostic with
  stage `hypothesis`, code `solution_count_mismatch` (exit 1).
* `cqr match <file> [--solutions M] [--text]` — check → extract → Algorithm 2 against the
  library. One match: `{pattern, subst, side_conditions}` JSON, exit 0. Otherwise one repair
  hint (Table 4; stage `match`, code `no_matching_pattern`), exit 1; `--text` prints it as text.
* `cqr synthesize <file> [--amax k] [--json] [--layers]` — check → `toNetwork` → oracle
  synthesis (report §6.1.4; straight-line, or Bennett pebbling of an AND chain when `k < ĉ∧`,
  §6.1.3). Prints `{name, schedule, and_complexity, grade: {w, d, t, a}}` (exit 0); `--json`
  adds the IR (`circuit`, the flat format of `tests/diff/`) and prints one line; `--layers`
  appends the layer dump of the depth scheduler. Failures: diagnostic JSON, exit 1.
* `cqr synthesize --diffusion n [--amax k] [--json] [--layers]` — the Grover diffusion on `n`
  data qubits (report §8.2; Stage 5b): V1 (straight-line MCZ) without `--amax`, V2 (Bennett
  MCZ) with it. Prints `{name, n, schedule, grade}`; `--json`/`--layers` as above.
* `cqr synthesize <file> --grover [--iterations r] [--solutions M] [--json] [--layers]` — the
  Grover circuit `H^{⊗n}` then `r` iterations of oracle ⊕ diffusion V1 (report §3.2.4, §8).
  Default `r = r⋆ = ⌊π/(4θ)⌋`, `sin²θ = M/2ⁿ` (M from ℰ or `--solutions`). Prints the grades of
  the oracle, the diffusion, one iteration (measured, and the ⊕ of the two measured parts) and
  the full circuit, and `r_star`; `--json` adds `circuit` and `iteration_circuit` (one line).
* `cqr emit <file> --format qir|qasm [--iterations r] [--solutions M] [--oracle]` — report
  §8.4.3 (Stage 8a): match (must be Grover), then print the QIR Adaptive Profile module or the
  OpenQASM 3 program of the Grover circuit (`r` as for `--grover`, default r⋆), with one
  terminal measurement of the data register. `--oracle` emits the phase oracle alone (for the
  differential test of the re-parsed program). Failures: diagnostic JSON, exit 1; no `r` and no
  M: message, exit 2. The emitters are unverified (§5.3); `tests/diff/` re-parses their output.
* `cqr certify <file> [--solutions M] [--iterations r] [--out dir] [--bench k]` — report §5.1.3,
  §8.4.1, §8.4.4, §9.5.1 (Stage 8b): match (must be Grover; otherwise the Table 4 hint, exit 1),
  synthesize, write `<dir>/Cert.lean` (default `certs/<name>/`; the specialization of the Grover
  parametric lemma), kernel-check it with `lake env lean` (run from the project root), audit the
  axioms of `#print axioms cert`, write `certificate.json`, `<name>.qir`, `<name>.qasm` from the
  same circuit and print the status line: `certified (conditional on: solution_count = M)`
  (exit 0) only if the kernel check and the audit pass; otherwise `certificate with tracked
  obligations: <list>` (exit 3). Kernel-check failure: message, exit 1, no JSON. `--bench k`:
  `k + 1` kernel checks, the median of the last `k` is recorded (scripts/bench_kernel.sh).
  Stage 9b: before writing anything, the front end is validated exhaustively for `n ≤ 16`
  (`validateFrontEnd`; a disagreement is a `front_end_mismatch` diagnostic, exit 1, nothing
  written) and `trust_boundary.front_end` says so. `--report` also writes `run_report.md` and
  `run_report.json` (Table 8.5.2, measured values; `CQRV.Certify.RunReport`).
-/

open CQRV CQRV.DSL CQRV.Matching CQRV.Synthesis CQRV.Certify CQRV.Emit

/-- Subcommands and the stage (docs/PLAN.md) that implements each. -/
def subcommands : List (String × Nat) :=
  [("check", 3), ("extract", 3), ("match", 4), ("synthesize", 5), ("certify", 8), ("emit", 8)]

def usage : String :=
  "usage: cqr <command> [args]\n\ncommands:\n" ++
    "  check <file>\n  extract <file> [--solutions M]\n  match <file> [--solutions M] [--text]\n" ++
    "  synthesize <file> [--amax k] [--json] [--layers]\n" ++
    "  synthesize --diffusion n [--amax k] [--json] [--layers]\n" ++
    "  synthesize <file> --grover [--iterations r] [--solutions M] [--json] [--layers]\n" ++
    "  check <file> --truth-table\n" ++
    "  certify <file> [--solutions M] [--iterations r] [--out dir] [--bench k] [--report]\n" ++
    "  emit <file> --format qir|qasm [--iterations r] [--solutions M] [--oracle]\n"

/-- Report §4.2.2 — parse and surface-check a source file; also returns the position of the
entry `fn` (the last one), used by the `--solutions` diagnostic. -/
def frontEnd (path : String) : IO (Except Diagnostic (TypedProgram × Pos)) := do
  let src ← IO.FS.readFile path
  return do
    let prog ← parse src
    let tp ← check prog
    return (tp, (prog.fns.getLast?.map (·.pos)).getD ⟨1, 1⟩)

/-- `cqr check <file>`. -/
def runCheck (path : String) : IO UInt32 := do
  match ← frontEnd path with
  | .ok _ => return 0
  | .error d => IO.println d.toJson.compress; return 1

/-- `cqr check <file> --truth-table` — report §5.3.3 (Stage 9b): the truth tables of the DSL
evaluator and of the network, for the differential harness. -/
def runTruthTable (path : String) : IO UInt32 := do
  match ← frontEnd path with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok (tp, _) =>
    if tp.hasLoop then
      IO.eprintln "cqr check --truth-table: `loop … while` has no finite truth table"; return 2
    match toNetwork tp with
    | .error d => IO.println d.toJson.compress; return 1
    | .ok N =>
      let n := N.nInputs
      if n > frontEndLimit then
        IO.eprintln s!"cqr check --truth-table: n = {n} > {frontEndLimit}"; return 2
      IO.println (Lean.Json.mkObj [("name", Lean.toJson tp.name), ("n", Lean.toJson n),
        ("evaluator", Lean.toJson (truthTable n (evalProgram tp))),
        ("network", Lean.toJson (truthTable n (N.pred n)))]).compress
      return 0

/-- Report §4.1.4, §7.2 — front end + ℰ + the `--solutions` hypothesis: the signature, or the
diagnostic to print (a front-end failure or `solution_count_mismatch`). -/
def signature (path : String) (solutions : Option Nat) : IO (Except Diagnostic SigmaIn) := do
  match ← frontEnd path with
  | .error d => return .error d
  | .ok (tp, p) =>
    let sig := extract tp
    match sig.solutionCount, solutions with
    | some m, some m' =>
      if m != m' then
        let msg := s!"--solutions {m'} contradicts the solution count {m} computed from the \
          predicate `{tp.name}` (report §4.1.4)"
        return .error (Diagnostic.at .hypothesis .solutionCountMismatch p msg)
      return .ok sig
    | _, _ => return .ok { sig with solutionCount := sig.solutionCount <|> solutions }

/-- `cqr extract <file> [--solutions M]`. -/
def runExtract (path : String) (solutions : Option Nat) : IO UInt32 := do
  match ← signature path solutions with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok sig => IO.println sig.toJson.pretty; return 0

/-- Report §4.3.2 — print the outcome of a failed match (Table 4 repair hint, as JSON or with
`text` as text); exit code 1. -/
def printNoMatch (cmd : String) (t : Term) (r : LibResult) (text : Bool) : IO UInt32 := do
  match r with
  | .noMatch _ _ _ _ dist =>
    let hs := renderHints t r
    if text then IO.print (hintsText hs dist)
    else
      match hs with
      | h :: _ => IO.println (h.toJson dist hs.length).compress
      | [] => IO.println "{}"
  | .empty => IO.eprintln s!"cqr {cmd}: the pattern library is empty"
  | .matched .. => pure ()
  return 1

/-- `cqr match <file> [--solutions M] [--text]` — report §4.2.4 (Algorithm 2), §4.3.2. -/
def runMatch (path : String) (solutions : Option Nat) (text : Bool) : IO UInt32 := do
  match ← signature path solutions with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok sig =>
    let t := sig.toTerm.normalize
    match matchLibrary library t with
    | .matched e σ ds => IO.println (matchJson e σ ds).pretty; return 0
    | r => printNoMatch "match" t r text

/-- Parse `[--solutions M] [--text]` in any order. -/
def matchFlags : List String → Option (Option Nat × Bool)
  | [] => some (none, false)
  | "--text" :: rest => (matchFlags rest).map fun (m, _) => (m, true)
  | "--solutions" :: m :: rest => do
    let k ← m.toNat?
    let (_, t) ← matchFlags rest
    return (some k, t)
  | _ => none

/-- Report §6.1.3–6.1.4 — the oracle circuit of a typed program under ancilla budget `aMax`
(`synthesizeWithBudget`: straight-line, or a Bennett pebbling of an AND chain). Returns the
schedule name and ĉ∧ of the network. -/
def synthesizeWith (tp : TypedProgram) (aMax : Option Nat) :
    Except Diagnostic (String × Nat × Circuit) := do
  let N ← toNetwork tp
  let (sched, c) ← synthesizeWithBudget N aMax
  return (sched, N.andCount, c)

/-- Report §3.1.1 — a grade as JSON `{w, d, t, a}`. -/
def gradeJson (g : Grade) : Lean.Json :=
  Lean.Json.mkObj [("w", g.w), ("d", g.d), ("t", g.t), ("a", g.a)]

/-- Print a result object: one compressed line with the IR fields `extra` under `--json`,
pretty otherwise; then the layer dump of `c` under `--layers`. -/
def printResult (base extra : List (String × Lean.Json)) (c : Circuit) (json layers : Bool) :
    IO Unit := do
  if json then IO.println (Lean.Json.mkObj (base ++ extra)).compress
  else IO.println (Lean.Json.mkObj base).pretty
  if layers then IO.println c.layerDump

/-- `cqr synthesize <file> [--amax k] [--json] [--layers]` — report §6.1.4, §6.3.1 (Eq. 5). -/
def runSynthesize (path : String) (aMax : Option Nat) (json layers : Bool) : IO UInt32 := do
  match ← frontEnd path with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok (tp, _) =>
    match synthesizeWith tp aMax with
    | .error d => IO.println d.toJson.compress; return 1
    | .ok (sched, cand, c) =>
      let base := [("name", Lean.toJson tp.name), ("schedule", Lean.toJson sched),
                   ("and_complexity", Lean.toJson cand), ("grade", gradeJson c.grade)]
      printResult base [("circuit", c.toJson)] c json layers
      return 0

/-- `cqr synthesize --diffusion n [--amax k] [--json] [--layers]` — report §8.2, Stage 5b. -/
def runDiffusion (n : Nat) (aMax : Option Nat) (json layers : Bool) : IO UInt32 := do
  match diffusionWith n aMax with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok (sched, c) =>
    let base := [("name", Lean.toJson "diffusion"), ("n", Lean.toJson n),
                 ("schedule", Lean.toJson s!"mcz {sched}"), ("grade", gradeJson c.grade)]
    printResult base [("circuit", c.toJson)] c json layers
    return 0

/-- `cqr synthesize <file> --grover [--iterations r] [--solutions M] [--json] [--layers]` —
report §3.2.4, §8 (Stage 5b): oracle ⊕ diffusion V1, `r` (default r⋆) iterations. -/
def runGrover (path : String) (iters solutions : Option Nat) (json layers : Bool) :
    IO UInt32 := do
  match ← frontEnd path, ← signature path solutions with
  | .error d, _ | _, .error d => IO.println d.toJson.compress; return 1
  | .ok (tp, _), .ok sig =>
    let n := sig.arity
    let rs := sig.solutionCount.bind (rStar n)
    let some r := iters <|> rs
      | IO.eprintln s!"cqr synthesize --grover: give --iterations r, or a solution count M \
          with 1 ≤ M ≤ 2^{n} (from ℰ or --solutions M) to compute r⋆"
        return 2
    let res : Except Diagnostic (Circuit × Circuit × Circuit × Circuit) := do
      let N ← toNetwork tp
      return (← synthesizeOracle N, ← diffusion n none, ← groverIteration N n,
        ← groverCircuit N n r)
    match res with
    | .error d => IO.println d.toJson.compress; return 1
    | .ok (o, d, it, g) =>
      let base := [("name", Lean.toJson tp.name), ("n", Lean.toJson n),
        ("solutions", Lean.toJson sig.solutionCount), ("r_star", Lean.toJson rs),
        ("iterations", Lean.toJson r),
        ("grades", Lean.Json.mkObj [("oracle", gradeJson o.grade),
          ("diffusion", gradeJson d.grade), ("iteration", gradeJson it.grade),
          ("oracle_plus_diffusion", gradeJson (o.grade + d.grade)),
          ("circuit", gradeJson g.grade)])]
      printResult base [("circuit", g.toJson), ("iteration_circuit", it.toJson)] g json layers
      return 0

/-- Parse `[--iterations r] [--solutions M] [--json] [--layers]` (after `--grover`). -/
def groverFlags : List String → Option (Option Nat × Option Nat × Bool × Bool)
  | [] => some (none, none, false, false)
  | "--json" :: rest => (groverFlags rest).map fun (r, m, _, l) => (r, m, true, l)
  | "--layers" :: rest => (groverFlags rest).map fun (r, m, j, _) => (r, m, j, true)
  | "--iterations" :: r :: rest => do
    let r ← r.toNat?
    let (_, m, j, l) ← groverFlags rest
    return (some r, m, j, l)
  | "--solutions" :: m :: rest => do
    let m ← m.toNat?
    let (r, _, j, l) ← groverFlags rest
    return (r, some m, j, l)
  | _ => none

/-- Parse `[--amax k] [--json] [--layers]` in any order. -/
def synthFlags : List String → Option (Option Nat × Bool × Bool)
  | [] => some (none, false, false)
  | "--json" :: rest => (synthFlags rest).map fun (k, _, l) => (k, true, l)
  | "--layers" :: rest => (synthFlags rest).map fun (k, j, _) => (k, j, true)
  | "--amax" :: k :: rest => do
    let k ← k.toNat?
    let (_, j, l) ← synthFlags rest
    return (some k, j, l)
  | _ => none

/-- Report §8.4.3 — output formats of `cqr emit`. -/
inductive EmitFormat where
  | qir
  | qasm

/-- Parse `--format qir|qasm [--iterations r] [--solutions M] [--oracle]` in any order. -/
def emitFlags : List String → Option (Option EmitFormat × Option Nat × Option Nat × Bool)
  | [] => some (none, none, none, false)
  | "--oracle" :: rest => (emitFlags rest).map fun (f, r, m, _) => (f, r, m, true)
  | "--format" :: f :: rest => do
    let f ← match f with | "qir" => some EmitFormat.qir | "qasm" => some .qasm | _ => none
    let (_, r, m, o) ← emitFlags rest
    return (some f, r, m, o)
  | "--iterations" :: r :: rest => do
    let r ← r.toNat?
    let (f, _, m, o) ← emitFlags rest
    return (f, some r, m, o)
  | "--solutions" :: m :: rest => do
    let m ← m.toNat?
    let (f, r, _, o) ← emitFlags rest
    return (f, r, some m, o)
  | _ => none

/-- `cqr emit <file> --format qir|qasm [--iterations r] [--solutions M] [--oracle]` — report
§8.4.3: the Grover circuit (or its oracle) of the matched instance as QIR or OpenQASM 3. -/
def runEmit (path : String) (fmt : EmitFormat) (iters solutions : Option Nat) (oracle : Bool) :
    IO UInt32 := do
  match ← frontEnd path, ← signature path solutions with
  | .error d, _ | _, .error d => IO.println d.toJson.compress; return 1
  | .ok (tp, _), .ok sig =>
    match groverInstance tp sig (if oracle then iters.getD 0 else iters) with
    | .error (.diagnostic d) => IO.println d.toJson.compress; return 1
    | .error (.usage msg) => IO.eprintln s!"cqr emit: {msg}"; return 2
    | .ok gi =>
      let (name, C) := if oracle then (s!"{tp.name}_oracle", gi.oracle) else (tp.name, gi.circuit)
      IO.print (match fmt with | .qir => emitQIR name C | .qasm => emitQASM name C)
      return 0

/-- Parse `[--solutions M] [--iterations r] [--out dir] [--bench k] [--report]` in any order. -/
def certifyFlags :
    List String → Option (Option Nat × Option Nat × Option String × Option Nat × Bool)
  | [] => some (none, none, none, none, false)
  | "--solutions" :: m :: rest => do
    let m ← m.toNat?
    let (_, r, o, b, p) ← certifyFlags rest
    return (some m, r, o, b, p)
  | "--iterations" :: r :: rest => do
    let r ← r.toNat?
    let (m, _, o, b, p) ← certifyFlags rest
    return (m, some r, o, b, p)
  | "--out" :: o :: rest => do
    let (m, r, _, b, p) ← certifyFlags rest
    return (m, r, some o, b, p)
  | "--bench" :: k :: rest => do
    let k ← k.toNat?
    guard (k ≥ 1)
    let (m, r, o, _, p) ← certifyFlags rest
    return (m, r, o, some k, p)
  | "--report" :: rest => (certifyFlags rest).map fun (m, r, o, b, _) => (m, r, o, b, true)
  | _ => none

/-- The median of a non-empty list (the lower middle element for an even length). -/
def median (xs : List Nat) : Nat :=
  let s := xs.mergeSort
  s.getD ((s.length - 1) / 2) 0

/-- Report §9.5.1 — the tracked obligations of a failed audit: every offending axiom by its
name, `sorryAx` first. Since Stage 9a the generator writes no `sorry` (Lemma 6.3.2 holds for XOR
networks), so a `sorryAx` is never explained by a generator obligation. -/
def obligationsOf (bad : List String) : List String :=
  (if bad.contains "sorryAx" then ["sorryAx"] else []) ++ bad.filter (· != "sorryAx")

/-- Milliseconds as seconds with two decimals. -/
def secs (ms : Nat) : String :=
  let c := (ms + 5) / 10
  s!"{c / 100}.{if c % 100 < 10 then "0" else ""}{c % 100} s"

/-- `cqr certify <file> [--solutions M] [--iterations r] [--out dir] [--bench k] [--report]` —
report §5.1.3, §8.4.1, §8.4.4, §9.5.1 (Stage 8b): check → extract → match → synthesize (`r = r⋆`
unless given) → front-end validation (Stage 9b) → generate `Cert.lean` → kernel check
(`lake env lean`) → axiom audit → write `certificate.json`, `<name>.qir`, `<name>.qasm` (from the
same circuit) and, with `--report`, `run_report.md` / `run_report.json` → status line.
`--bench k` repeats the kernel check `k + 1` times and records the median of the last `k`. -/
def runCertify (path : String) (solutions iters : Option Nat) (out : Option String)
    (bench : Option Nat) (report : Bool) : IO UInt32 := do
  let src ← IO.FS.readFile path
  match ← frontEnd path, ← signature path solutions with
  | .error d, _ | _, .error d => IO.println d.toJson.compress; return 1
  | .ok (tp, entryPos), .ok sig =>
    let t := sig.toTerm.normalize
    let (subst, sides) ← match matchLibrary library t with
      | .matched _ σ ds =>
        let σs := σ.mergeSort fun a b => Term.MVar.cmp a.1 b.1 != .gt
        pure (", ".intercalate (σs.map fun (m, b) => s!"{m.name} ↦ {b.toJson.compress}"),
          ds.map fun d => s!"{d.cond.render}: {d.render}")
      | r => return (← printNoMatch "certify" t r false)
    let gi ← match groverInstance tp sig iters with
      | .ok gi => pure gi
      | .error (.diagnostic d) => IO.println d.toJson.compress; return 1
      | .error (.usage msg) => IO.eprintln s!"cqr certify: {msg}"; return 2
    let some M := gi.M
      | IO.eprintln "cqr certify: the certificate needs the solution count M (--solutions M)"
        return 2
    -- front-end validation (Stage 9b, decision 1): before anything is written
    let fe := validateFrontEnd tp gi.net gi.n
    let some feText := fe.trustText
      | match fe.diagnostic? tp.name entryPos with
        | some d => IO.println d.toJson.compress; return 1
        | none => return 1
    let cfg ← match RefConfig.ofFiles (← IO.FS.readFile "lean-toolchain")
        (← IO.FS.readFile "lake-manifest.json") with
      | .ok c => pure c
      | .error e => IO.eprintln s!"cqr certify: {e}"; return 2
    let q := CertRequest.ofInstance tp.name src gi M
    let text := renderCert q
    let dir := (out.getD s!"certs/{tp.name}").dropEndWhile (fun c => c == '/' || c == '\\')
    let file (n : String) : String := s!"{dir}/{n}"
    IO.FS.createDirAll dir.toString
    let certPath := file "Cert.lean"
    IO.FS.writeFile certPath text
    -- kernel check and audit (decisions 2, 3); with --bench, k + 1 runs, the first discarded
    let mut outcomes : Array AuditOutcome := #[]
    for _ in [0:(bench.map (· + 1)).getD 1] do
      match ← checkAndAudit certPath q.theoremName with
      | .ok o => outcomes := outcomes.push o
      | .error e => IO.eprintln s!"cqr certify: {certPath}: {e}"; return 1
    let some last := outcomes.back? | return 1
    let timed := if bench.isSome then outcomes.toList.drop 1 else outcomes.toList
    let kernels := timed.filterMap (·.check.kernelMs)
    let timing : KernelTiming :=
      { wallMs := median (timed.map (·.check.wallMs)),
        kernelMs := if kernels.length == timed.length then some (median kernels) else none,
        runs := timed.length,
        statistic := match bench with
          | some k => s!"median of {k} (first run excluded)"
          | none => "single run" }
    let (status, obligations) := match last.result with
      | .pass => (Status.certified, [])
      | .fail bad => (Status.withObligations, obligationsOf bad)
    let (cpu, cpus, clock) ← detectMachine
    let cfg := { cfg with cpu := some (cpu.getD "unknown"), logicalCpus := cpus, clock,
                          leanThreads := ← IO.getEnv "LEAN_NUM_THREADS", kernelCheck := timing }
    let base ← match Certificate.build src sig gi.entry gi.facts gi.circuit gi.circuit.grade gi.r
        gi.n M q.delta cfg feText with
      | .ok c => pure c
      | .error e => IO.eprintln s!"cqr certify: {e}"; return 1
    let cert := { base with
      proofHash := some (proofHash text cfg.lean cfg.mathlib cfg.physlib), axioms := last.axioms,
      status, theoremName := some q.theoremName, obligations }
    -- compact, keys sorted (canonical, as `circuit_hash` and `CertifyTool sample`)
    IO.FS.writeFile (file "certificate.json") (cert.toJson.compress ++ "\n")
    IO.FS.writeFile (file s!"{tp.name}.qir") (emitQIR tp.name gi.circuit)
    IO.FS.writeFile (file s!"{tp.name}.qasm") (emitQASM tp.name gi.circuit)
    let statusLine := match status with
      | .certified => s!"certified (conditional on: solution_count = {M})"
      | _ => s!"certificate with tracked obligations: {", ".intercalate obligations}"
    if report then
      let dif ← match diffusion gi.n none with
        | .ok c => pure c
        | .error d => IO.println d.toJson.compress; return 1
      let rd : RunData :=
        { name := tp.name, source := path, predicateHash := cert.predicateHash, sig,
          pattern := gi.entry.name, subst, sides, net := gi.net, oracle := gi.oracle,
          diffusion := dif, circuit := gi.circuit, n := gi.n, M, r := gi.r, delta := q.delta,
          frontEnd := fe, theoremName := q.theoremName, certPath, timing,
          axioms := last.axioms, statusLine, certified := status == .certified }
      IO.FS.writeFile (file "run_report.md") rd.toMarkdown
      IO.FS.writeFile (file "run_report.json") (rd.toJson.pretty ++ "\n")
    let kms := match timing.kernelMs with | some k => s!", {secs k} kernel" | none => ""
    IO.println s!"kernel check: {certPath} (exit 0, {secs timing.wallMs} wall{kms}; \
      {timing.statistic})"
    IO.println s!"axioms: {", ".intercalate last.axioms}"
    IO.println s!"wrote: {file "certificate.json"}, {file s!"{tp.name}.qir"}, \
      {file s!"{tp.name}.qasm"}{if report then s!", {file "run_report.md"}, \
      {file "run_report.json"}" else ""}"
    IO.println s!"front end: {feText}"
    IO.println statusLine
    return if status == .certified then 0 else 3

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", file] => runCheck file
  | ["check", file, "--truth-table"] => runTruthTable file
  | ["extract", file] => runExtract file none
  | ["extract", file, "--solutions", m] =>
    match m.toNat? with
    | some m => runExtract file (some m)
    | none => IO.eprintln s!"cqr extract: --solutions expects a natural number, got `{m}`"; return 2
  | "match" :: file :: flags =>
    match matchFlags flags with
    | some (m, t) => runMatch file m t
    | none => IO.eprint usage; return 2
  | "synthesize" :: "--diffusion" :: n :: flags =>
    match n.toNat?, synthFlags flags with
    | some n, some (k, j, l) => runDiffusion n k j l
    | _, _ => IO.eprint usage; return 2
  | "synthesize" :: file :: "--grover" :: flags =>
    match groverFlags flags with
    | some (r, m, j, l) => runGrover file r m j l
    | none => IO.eprint usage; return 2
  | "synthesize" :: file :: flags =>
    match synthFlags flags with
    | some (k, j, l) => runSynthesize file k j l
    | none => IO.eprint usage; return 2
  | "certify" :: file :: flags =>
    match certifyFlags flags with
    | some (m, r, o, b, p) => runCertify file m r o b p
    | none => IO.eprint usage; return 2
  | "emit" :: file :: flags =>
    match emitFlags flags with
    | some (some f, r, m, o) => runEmit file f r m o
    | _ => IO.eprint usage; return 2
  | cmd :: _ =>
    match subcommands.lookup cmd with
    | some stage =>
      if stage ≤ 5 || cmd == "emit" || cmd == "certify" then IO.eprint usage; return 2
      IO.eprintln s!"cqr {cmd}: not implemented (Stage {stage})"
      return 2
    | none =>
      IO.eprint usage
      return 2
  | [] =>
    IO.eprint usage
    return 2
