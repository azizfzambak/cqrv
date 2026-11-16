import CQRV.DSL.Basic
import CQRV.Matching.Basic
import CQRV.Synthesis.Basic
import CQRV.Certify.Basic
import CQRV.Emit.Basic
import CQRV.Patterns.Basic
import CQRV.Patterns.Select
import CQRV.Hardware.Target
import CQRV.Hardware.Bound
import CQRV.Hardware.Decomp
import CQRV.Hardware.CheckGen
import CQRV.Hardware.PhysGrade
import CQRV.Hardware.Noise
import CQRV.Hardware.NoiseCertGen

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
* `cqr extract <file> [--solutions M] [--problem search|count] [--precision m]` — print the
  `SigmaIn` JSON (exit 0), or the diagnostic
  JSON (exit 1). `--solutions M` supplies the ground solution count when ℰ cannot compute it
  (DECISIONS.md 2026-10-23, decision 5); a value that contradicts ℰ's is a diagnostic with
  stage `hypothesis`, code `solution_count_mismatch` (exit 1).
* `cqr match <file> [--solutions M] [--text] [--problem search|count] [--precision m]` — check →
  extract → Algorithm 2 against the
  library. One match: `{pattern, subst, side_conditions}` JSON, exit 0. Otherwise one repair
  hint (Table 4; stage `match`, code `no_matching_pattern`), exit 1; `--text` prints it as text.
* `cqr synthesize <file> [--amax k] [--uncompute mbu|coherent] [--json] [--layers]` — check →
  `toNetwork` → oracle (`--uncompute coherent`: the adjoint uncompute of PHASE2_SPEC.md §A.0.1,
  Stage 15a; MBU-only paths — Bennett below the straight-line count, `few:` shapes — are
  `unsupported_combination`)
  synthesis (report §6.1.4; straight-line, or Bennett pebbling of an AND chain when `k < ĉ∧`,
  §6.1.3). Prints `{name, schedule, and_complexity, grade: {w, d, t, a}}` (exit 0); `--json`
  adds the IR (`circuit`, the flat format of `tests/diff/`) and prints one line; `--layers`
  appends the layer dump of the depth scheduler. Failures: diagnostic JSON, exit 1.
* `cqr synthesize --diffusion n [--shape tree|chain|few:ladder|few:log] [--amax k] [--json]
  [--layers]` — the Grover diffusion on `n` data qubits (report §8.2; Stage 5b): V1
  (straight-line MCZ) without `--amax`, V2 (Bennett MCZ, chain only) with it. The MCZ network is
  the balanced AND tree unless `--shape chain` (Stage 12a). `--shape few:<variant>` (Stage 12b)
  uses the few-ancilla MCZ `mczFew` (no `--amax`); its output carries `status` =
  `MczVariant.status` (Stage 13a′: `few:log` "restoration proved for every n (Stage 13a);
  certified via `cqr certify --shape few:log`", `few:ladder` "classical step checked at n = 8,
  restoration not certified"). Prints `{name, n, shape, schedule, grade}`;
  `--json`/`--layers` as above.
* `cqr synthesize <file> --grover [--shape tree|chain|few:ladder|few:log] [--iterations r]
  [--solutions M] [--json] [--layers]` — the Grover circuit `H^{⊗n}` then `r` iterations of
  oracle ⊕ diffusion V1 (report §3.2.4, §8; tree diffusion by default, Stage 12a; a `few:` shape
  carries its `status`, Stage 12b / 12d).
  Default `r = r⋆ = ⌊π/(4θ)⌋`, `sin²θ = M/2ⁿ` (M from ℰ or `--solutions`). Prints the grades of
  the oracle, the diffusion, one iteration (measured, and the ⊕ of the two measured parts) and
  the full circuit, and `r_star`; `--json` adds `circuit` and `iteration_circuit` (one line).
* `cqr hw capabilities <target.json>` — Stage 24a (PHASE2_SPEC §C.1): the capability flags of
  a hardware target with their sources, the uncomputation modes it supports, and the snapshot
  hash check (exit 0 ok, 1 mismatch, 2 usage / unreadable target).
* `cqr hw bound <file.cqr> --target <target.json> …` — Stage 24c (PHASE2_SPEC §C.1): the weighted
  bound δ_hw ≤ δ + Σ_types count · rate of the Grover circuit (the same `groverInstance` as
  `cqr certify`) under the decomposition table of the target's basis, with the worst-case rates
  over the device (a bound for any layout, marked vacuous at ≥ 1) and the median figure (typical,
  not a bound); reported, not certified. Exit 2: usage, an unreadable target, or `mbu` on a target
  without feed-forward.
* `cqr hw table --basis cz|cx` — Stage 26a (PHASE2_SPEC §C.3): the Lean decomposition table
  (`CQRV.Hardware.decompTable`) as JSON in `hw/decomp.py --json`'s format, compared by the harness.
* `cqr emit <file> --format qir|qasm [--iterations r] [--solutions M] [--oracle]` — report
  §8.4.3 (Stage 8a): match (must be Grover), then print the QIR Adaptive Profile module or the
  OpenQASM 3 program of the Grover circuit (`r` as for `--grover`, default r⋆), with one
  terminal measurement of the data register. `--oracle` emits the phase oracle alone (for the
  differential test of the re-parsed program). Failures: diagnostic JSON, exit 1; no `r` and no
  M: message, exit 2. The emitters are unverified (§5.3); `tests/diff/` re-parses their output.
  Stage 17b (PHASE2_SPEC.md §A.1): the phase gates `p a k` / `cp a k` are `p(2*pi*a/2^k)` /
  `cp(…)` in OpenQASM 3 (the power evaluated) and, in QIR, `rz` with a hex-float angle and the
  five-gate `decomposeCp`; a `cp` under `ifBit` has no QIR form: diagnostic `unsupported_in_qir`
  (stage `emit`), exit 1, nothing written (no synthesized circuit contains these gates; the
  sample circuit of `scripts/CertifyTool.lean emit-sample` exercises them).
* `cqr certify <file> [--solutions M] [--iterations r] [--out dir] [--bench k]` — report §5.1.3,
  §8.4.1, §8.4.4, §9.5.1 (Stage 8b): match (must be Grover; otherwise the Table 4 hint, exit 1),
  synthesize, write `<dir>/Cert.lean` (default `certs/<name>/`; the specialization of the Grover
  parametric lemma), kernel-check it with `lake env lean` (run from the project root), audit the
  axioms of `#print axioms cert`, write `certificate.json`, `<name>.qir`, `<name>.qasm` from the
  same circuit and print the status line: `certified` (Stage 14a, `n ≤ --count-limit`) or
  `certified (conditional on: solution_count = M)`
  (exit 0) only if the kernel check and the audit pass; otherwise `certificate with tracked
  obligations: <list>` (exit 3). Kernel-check failure: message, exit 1, no JSON. `--bench k`:
  `k + 1` kernel checks, the median of the last `k` is recorded (scripts/bench_kernel.sh).
  Stage 16b: `Cert.lean` states the front end at the instance (`prog`, the typed-term literal;
  `prog_scoped`; `net_ok : toNetwork prog = .ok net`; `front_end` from `toNetwork_pred`, all
  kernel-checked) and `trust_boundary.front_end` says so (schema 1.8.0, `uncompute` explicit);
  the Stage 9b exhaustive validation (`validateFrontEnd`, `front_end_mismatch`) is no longer run
  by `certify` (`cqr check --truth-table` keeps it). `--report` also writes `run_report.md` and
  `run_report.json` (Table 8.5.2, measured values; `CQRV.Certify.RunReport`). Stage 17b: every
  `Cert.lean` states `gradeExt_eq` (the second record `GradeExt`, right after `grade_eq`) and
  `certificate.json` records it as `grade_ext` (schema 1.9.0); the run report prints it in row 4.
  Stage 11b: `--profile <name|path>` (`profiles/<name>.json`, or a path) checks the measured
  grade against the declared budget and computes `δ_hw = δ + G·p̄` (report §3.3.2–3.3.3);
  `certificate.json` gets the object `hardware` (schema v1.4.0), the run report a row
  "Hardware profile", and a second line after the status line says whether the grade fits and
  whether the bound is vacuous. Hardware fitness is not part of "certified" and does not change
  the exit code; a profile that cannot be read: message, exit 2, nothing written. Without
  `--profile` every output is as before.
  Stage 14a: `--count-limit k` (default 10, Stage 14c; `0` disables). For `n ≤ k` the tool evaluates
  `Network.countSat net n` itself; if it differs from the supplied or extracted `M` it prints the
  diagnostic `solution_count_mismatch` (stage `hypothesis`; supplied M, computed count) and
  writes nothing (exit 1); otherwise `Cert.lean` proves `hM_count` by `Network.countSat_eq_card`
  and `decide +kernel`, `theorem cert` takes no hypothesis, and the status line is `certified`.
  For `n > k` the conditional form stays: `certified (conditional on: solution_count = M)`.
  `certificate.json` records `solution_count: {value, status}` (`kernel_decided` / `hypothesis`).
-/

open CQRV CQRV.DSL CQRV.Matching CQRV.Synthesis CQRV.Certify CQRV.Emit CQRV.Patterns

/-- Subcommands and the stage (docs/PLAN.md) that implements each. -/
def subcommands : List (String × Nat) :=
  [("check", 3), ("extract", 3), ("match", 4), ("synthesize", 5), ("certify", 8), ("emit", 8),
   ("hw", 24)]

def usage : String :=
  "usage: cqr <command> [args]\n\ncommands:\n" ++
    "  check <file>\n  extract <file> [--solutions M] [--problem search|count] [--precision m]\n" ++
    "  match <file> [--solutions M] [--text] [--problem search|count] [--precision m]\n" ++
    "  synthesize <file> [--amax k] [--uncompute mbu|coherent] [--json] [--layers]\n" ++
    "  synthesize --diffusion n [--shape tree|chain|few:ladder|few:log] [--amax k] [--uncompute mbu|coherent] [--json] [--layers]\n" ++
    "  synthesize <file> --grover [--shape tree|chain|few:ladder|few:log] [--iterations r] [--solutions M] [--uncompute mbu|coherent] [--json] [--layers]\n" ++
    "  check <file> --truth-table\n" ++
    "  certify <file> [--solutions M] [--iterations r] [--out dir] [--bench k] [--report]\n" ++
    "          [--profile name|path] [--shape tree|few:log] [--count-limit k] [--uncompute mbu|coherent]\n" ++
    "  certify <file> --problem count --precision m [--out dir] [--bench k] [--report]\n" ++
    "          [--count-limit k] [--uncompute mbu|coherent]\n" ++
    "  certify <file> --budget w,d,t,a --prefer width|depth|t|anc [--solutions M] [--iterations r]\n" ++
    "          [--count-limit k] [--profile name|path] [--bench k] [--report] [--out dir]\n" ++
    "  emit <file> --format qir|qasm [--iterations r] [--solutions M] [--oracle]\n" ++
    "  hw capabilities <target.json>\n" ++
    "  hw bound <file.cqr> --target <target.json> [--solutions M] [--iterations r] [--shape tree|few:log]\n" ++
    "          [--uncompute mbu|coherent] [--json]\n" ++
    "  hw table --basis cz|cx\n" ++
    "  hw check --artifact <dir> --target <target.json> [--out <dir>]\n" ++
    "  hw grade --artifact <dir> --target <target.json> --ff-latency <ns> [--json]\n" ++
    "  hw certify --cert <dir> --artifact <dir> --target <target.json> --ff-latency <ns> [--out <dir>]\n" ++
    "  hw select --request <name> --target <target.json> --prefer twoq|depth|bound|noise [--ff-latency <ns>] [--budget X] [--out <dir>] [--table]\n" ++
    "  hw noise --artifact <dir> --target <target.json> [--json]\n" ++
    "  hw noisecert --artifact <dir> --target <target.json> --ff-latency <ns> [--cert <dir>] [--out <dir>]\n"

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

/-- `cqr extract <file> [--solutions M] [--problem search|count] [--precision m]` — PHASE2_SPEC.md
§A.5 (amendments before Stage 21, (3)): the request's problem is applied to ℰ's signature
(`SigmaIn.withProblem`; `search` is the identity, so the Phase 1 output is unchanged). -/
def runExtract (path : String) (solutions : Option Nat) (problem : Problem := .search) :
    IO UInt32 := do
  match ← signature path solutions with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok sig => IO.println (sig.withProblem problem).toJson.pretty; return 0

/-- Report §4.3.2 — print the outcome of a failed match (Table 4 repair hint, as JSON or with
`text` as text); exit code 1. Stage 21a2 (PHASE2_SPEC §A.5 amendment (4)): the non-match is
proved — `matchLibrary_spec` (Proposition 5.1, `CQRV/Matching/Complete.lean`) says that a
non-`matched` result on the ground term `t` (`SigmaIn.toTerm_ground`) means that no library entry
matches; the text ends with that line and the JSON carries `non_match: proved`. -/
def printNoMatch (cmd : String) (t : Term) (r : LibResult) (text : Bool) : IO UInt32 := do
  match r with
  | .noMatch _ _ _ _ dist =>
    let hs := renderHints t r
    if text then
      IO.print (hintsText hs dist)
      IO.println "No library entry matches (proved: Proposition 5.1, matchLibrary_spec)."
    else
      match hs with
      | h :: _ => IO.println (h.toJson dist hs.length).compress
      | [] => IO.println "{}"
  | .empty => IO.eprintln s!"cqr {cmd}: the pattern library is empty"
  | .matched .. => pure ()
  return 1

/-- `cqr match <file> [--solutions M] [--text] [--problem search|count] [--precision m]` — report
§4.2.4 (Algorithm 2), §4.3.2; PHASE2_SPEC.md §A.5 (amendments before Stage 21, (3)): the
request's problem is applied to ℰ's signature before the term is built. -/
def runMatch (path : String) (solutions : Option Nat) (text : Bool)
    (problem : Problem := .search) : IO UInt32 := do
  match ← signature path solutions with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok sig =>
    let t := (sig.withProblem problem).toTerm.normalize
    match matchLibrary library t with
    | .matched e σ ds => IO.println (matchJson e σ ds).pretty; return 0
    | r => printNoMatch "match" t r text

/-- The request flags of `extract` / `match` (Stage 21a1): `--solutions M`, `--text` (`match`
only), `--problem search|count`, `--precision m`, in any order. -/
structure RequestFlags where
  solutions : Option Nat := none
  text : Bool := false
  problem : Option String := none
  precision : Option Nat := none

/-- Parse the request flags in any order; `none` on an unknown flag, a missing or non-numeric
value, or a repeated flag. -/
def requestFlags (allowText : Bool) : List String → Option RequestFlags
  | [] => some {}
  | "--text" :: rest => do
    if !allowText then none
    let f ← requestFlags allowText rest
    if f.text then none
    return { f with text := true }
  | "--solutions" :: m :: rest => do
    let k ← m.toNat?
    let f ← requestFlags allowText rest
    if f.solutions.isSome then none
    return { f with solutions := some k }
  | "--problem" :: p :: rest => do
    if p != "search" && p != "count" then none
    let f ← requestFlags allowText rest
    if f.problem.isSome then none
    return { f with problem := some p }
  | "--precision" :: m :: rest => do
    let k ← m.toNat?
    let f ← requestFlags allowText rest
    if f.precision.isSome then none
    return { f with precision := some k }
  | _ => none

/-- PHASE2_SPEC.md §A.5 (amendments before Stage 21, (3)) — the problem of a request from its
flags: `--problem count` needs `--precision m`, and `--precision` needs `--problem count`
(both usage errors); `--problem search` and no flag are `search`. -/
def problemOf (f : RequestFlags) : Option Problem :=
  match f.problem, f.precision with
  | some "count", some m => some (.count m)
  | some "count", none => none
  | _, some _ => none
  | _, none => some .search

/-- Parse `[--solutions M] [--text]` in any order (the Stage 4 parser of `match`, kept for the
search path: a flag list without `--problem` / `--precision` is parsed as before). -/
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
def synthesizeWith (tp : TypedProgram) (aMax : Option Nat) (mode : UncomputeMode := .mbu) :
    Except Diagnostic (String × Nat × Circuit) := do
  let N ← toNetwork tp
  let (sched, c) ← synthesizeWithBudget N aMax mode
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

/-- `cqr synthesize <file> [--amax k] [--uncompute mbu|coherent] [--json] [--layers]` — report
§6.1.4, §6.3.1 (Eq. 5); `--uncompute` PHASE2_SPEC.md §A.0.1 (Stage 15a). -/
def runSynthesize (path : String) (aMax : Option Nat) (mode : UncomputeMode) (json layers : Bool) :
    IO UInt32 := do
  match ← frontEnd path with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok (tp, _) =>
    match synthesizeWith tp aMax mode with
    | .error d => IO.println d.toJson.compress; return 1
    | .ok (sched, cand, c) =>
      let base := [("name", Lean.toJson tp.name), ("schedule", Lean.toJson sched),
                   ("and_complexity", Lean.toJson cand), ("grade", gradeJson c.grade)]
      printResult base [("circuit", c.toJson)] c json layers
      return 0

/-- The `--shape` of the CLI: a proved diffusion shape (Stage 12a) or a few-ancilla MCZ variant
(Stage 12b; status per variant, Stage 12d). -/
inductive ShapeArg where
  | std (s : DiffusionShape)
  | few (v : MczVariant)

/-- The name of a diffusion shape in the CLI and its JSON (`tree`, `chain`, `few:ladder`,
`few:log`). -/
def shapeName : ShapeArg → String
  | .std .tree => "tree"
  | .std .chain => "chain"
  | .few v => s!"few:{v.name}"

/-- The `status` field of a few-ancilla shape (Stage 12b decision 4; Stage 12d decision 5:
`MczVariant.status` of the variant); empty for the V1 shapes, whose output is unchanged. -/
def shapeStatus : ShapeArg → List (String × Lean.Json)
  | .std _ => []
  | .few v => [("status", Lean.toJson v.status)]

/-- The diffusion `cqr certify --shape` accepts (Stage 12d decision 3): the tree (default) or
`few:log`; `chain` and `few:ladder` have no certificate path (usage error). -/
def certDiffusionOf : ShapeArg → Option CertDiffusion
  | .std .tree => some .tree
  | .few .logDepth => some .fewLog
  | _ => none

/-- Parse a `--shape` value. -/
def shapeOf : String → Option ShapeArg
  | "tree" => some (.std .tree)
  | "chain" => some (.std .chain)
  | "few:ladder" => some (.few .ladder)
  | "few:log" => some (.few .logDepth)
  | _ => none

/-- Remove `--shape tree|chain|few:ladder|few:log` from the flags (Stage 12a decision 3, Stage
12b decision 4; default `tree`). -/
def shapeFlag : List String → Option (ShapeArg × List String)
  | [] => some (.std .tree, [])
  | "--shape" :: s :: rest => do
    let sh ← shapeOf s
    let (_, fs) ← shapeFlag rest
    return (sh, fs)
  | f :: rest => (shapeFlag rest).map fun (sh, fs) => (sh, f :: fs)

/-- `cqr synthesize --diffusion n [--shape tree|chain|few:ladder|few:log] [--amax k] [--json]
[--layers]` — report §8.2, Stage 5b; the MCZ network is the balanced tree unless `--shape chain`
(Stage 12a); `few:<variant>` is the unproved few-ancilla MCZ (Stage 12b, no `--amax`). -/
def runDiffusion (n : Nat) (aMax : Option Nat) (shape : ShapeArg) (mode : UncomputeMode)
    (json layers : Bool) : IO UInt32 := do
  let res : Except Diagnostic (String × Circuit) := match shape with
    | .std sh => diffusionWith n aMax sh mode
    | .few v => do
      if aMax.isSome then
        Diffusion.fail .unsupportedNetwork s!"--amax does not apply to --shape few:{v.name}"
      if mode == .coherent then
        Diffusion.fail .unsupportedCombination s!"the few-ancilla MCZ is MBU-only (Stage 15): \
          --shape few:{v.name} does not take --uncompute coherent"
      return (s!"few:{v.name} ({v.source})", ← diffusionFew n v)
  match res with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok (sched, c) =>
    let base := [("name", Lean.toJson "diffusion"), ("n", Lean.toJson n),
                 ("shape", Lean.toJson (shapeName shape))] ++ shapeStatus shape ++
                [("schedule", Lean.toJson s!"mcz {sched}"), ("grade", gradeJson c.grade)]
    printResult base [("circuit", c.toJson)] c json layers
    return 0

/-- `cqr synthesize <file> --grover [--shape tree|chain|few:ladder|few:log] [--iterations r]
[--solutions M] [--json] [--layers]` — report §3.2.4, §8 (Stage 5b): oracle ⊕ diffusion V1, `r`
(default r⋆) iterations; balanced-tree diffusion unless `--shape chain` (Stage 12a); `few:` shapes
are unproved (Stage 12b). -/
def runGrover (path : String) (iters solutions : Option Nat) (shape : ShapeArg)
    (mode : UncomputeMode) (json layers : Bool) : IO UInt32 := do
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
      match shape with
      | .std sh =>
        return (← synthesizeOracle N mode, ← diffusion n none sh mode,
          ← groverIteration N n none sh mode, ← groverCircuit N n r none sh mode)
      | .few v =>
        if mode == .coherent then
          Diffusion.fail .unsupportedCombination s!"the few-ancilla MCZ is MBU-only (Stage 15): \
            --shape few:{v.name} does not take --uncompute coherent"
        return (← synthesizeOracle N, ← diffusionFew n v, ← groverIterationFew N n v,
          ← groverCircuitFew N n r v)
    match res with
    | .error d => IO.println d.toJson.compress; return 1
    | .ok (o, d, it, g) =>
      let base := [("name", Lean.toJson tp.name), ("n", Lean.toJson n),
        ("shape", Lean.toJson (shapeName shape))] ++ shapeStatus shape ++
        [("solutions", Lean.toJson sig.solutionCount), ("r_star", Lean.toJson rs),
        ("iterations", Lean.toJson r),
        ("grades", Lean.Json.mkObj [("oracle", gradeJson o.grade),
          ("diffusion", gradeJson d.grade), ("iteration", gradeJson it.grade),
          ("oracle_plus_diffusion", gradeJson (o.grade + d.grade)),
          ("circuit", gradeJson g.grade)])]
      printResult base [("circuit", g.toJson), ("iteration_circuit", it.toJson)] g json layers
      return 0

/-- Remove `--uncompute mbu|coherent` from the flags (PHASE2_SPEC.md §A.0.1, Stage 15a); the
default is `mbu`; an unknown value is a usage error. -/
def uncomputeFlag : List String → Option (UncomputeMode × List String)
  | [] => some (.mbu, [])
  | "--uncompute" :: m :: rest => do
    let mode ← UncomputeMode.parse? m
    let (_, rest) ← uncomputeFlag rest
    return (mode, rest)
  | f :: rest => (uncomputeFlag rest).map fun (m, r) => (m, f :: r)

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

/-- Parse `[--amax k] [--json] [--layers]` in any order (`--uncompute` is removed first by
`uncomputeFlag`). -/
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
    | .error (.diagnostic d) =>
      -- Stage 21a2 (PHASE2_SPEC §A.5 amendment (4)): the no-match diagnostic of `groverInstance`
      -- carries `non_match: proved` like the hint of `cqr match` (`matchLibrary_spec`).
      let j := if d.code = .noMatchingPattern then d.toJson.setObjVal! "non_match" "proved"
        else d.toJson
      IO.println j.compress; return 1
    | .error (.usage msg) => IO.eprintln s!"cqr emit: {msg}"; return 2
    | .ok gi =>
      let (name, C) := if oracle then (s!"{tp.name}_oracle", gi.oracle) else (tp.name, gi.circuit)
      match fmt with
      | .qasm => IO.print (emitQASM name C); return 0
      | .qir =>
        match emitQIR name C with
        | .ok text => IO.print text; return 0
        | .error d => IO.println d.toJson.compress; return 1

/-- Parse `[--solutions M] [--iterations r] [--out dir] [--bench k] [--report]
[--profile name|path] [--count-limit k]` in any order. -/
def certifyFlags : List String →
    Option (Option Nat × Option Nat × Option String × Option Nat × Bool × Option String ×
      Option Nat)
  | [] => some (none, none, none, none, false, none, none)
  | "--solutions" :: m :: rest => do
    let m ← m.toNat?
    let (_, r, o, b, p, h, c) ← certifyFlags rest
    return (some m, r, o, b, p, h, c)
  | "--iterations" :: r :: rest => do
    let r ← r.toNat?
    let (m, _, o, b, p, h, c) ← certifyFlags rest
    return (m, some r, o, b, p, h, c)
  | "--out" :: o :: rest => do
    let (m, r, _, b, p, h, c) ← certifyFlags rest
    return (m, r, some o, b, p, h, c)
  | "--bench" :: k :: rest => do
    let k ← k.toNat?
    guard (k ≥ 1)
    let (m, r, o, _, p, h, c) ← certifyFlags rest
    return (m, r, o, some k, p, h, c)
  | "--report" :: rest =>
    (certifyFlags rest).map fun (m, r, o, b, _, h, c) => (m, r, o, b, true, h, c)
  | "--profile" :: h :: rest => do
    let (m, r, o, b, p, _, c) ← certifyFlags rest
    return (m, r, o, b, p, some h, c)
  | "--count-limit" :: k :: rest => do
    let k ← k.toNat?
    let (m, r, o, b, p, h, _) ← certifyFlags rest
    return (m, r, o, b, p, h, some k)
  | _ => none

/-- Stage 14c — the default of `--count-limit`: the solution count is decided by the kernel for
`n ≤ 10`. Stage 14a set 12 (DECISIONS.md 2026-10-29); Stage 14b measured every n = 12
kernel-decided certificate timing out at 900 s, while n = 10 (carry_5) takes 103 s median and
11 371 MB (docs/benchmarks/SCALING.md; DECISIONS.md 2026-10-30). -/
def defaultCountLimit : Nat := 10

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

/-- The certificate of a matched Grover instance `gi` (the tail of `cqr certify`, from the solution
count to the status line): `Cert.lean`, the kernel check and the audit, `certificate.json`, the
QIR / QASM texts and the run report. Stage 21a4 (PHASE2_SPEC.md §A.6 (8), (8′)): with `sel`, the
selection block is appended to `Cert.lean`, `chosen_fits` and `selected` are audited in the same
kernel run, the JSON carries `selection` (schema 1.11.0), the report a selection row, and the
`selection:` line follows the status line; without `sel` the output is byte for byte that of the
ordinary path. -/
def certifyGrover (path src : String) (tp : TypedProgram) (entryPos : Pos) (sig : SigmaIn)
    (subst : String) (sides : List String) (gi : GroverInstance) (solutions : Option Nat)
    (out : Option String) (bench : Option Nat) (report : Bool) (profile : Option String)
    (diff : CertDiffusion) (countLimit : Nat) (mode : UncomputeMode)
    (sel : Option SelectionInfo) : IO UInt32 := do
    let some M := gi.M
      | IO.eprintln "cqr certify: the certificate needs the solution count M (--solutions M)"
        return 2
    -- the front end (Stage 16b): a theorem of Cert.lean (`front_end`), declared as such
    let feText := frontEndProvedText
    -- the solution count (Stage 14a): for n ≤ --count-limit, counted here and decided by the
    -- kernel in Cert.lean (`hM_count`); a mismatch with the supplied / extracted M writes nothing
    let count : CountStatus ←
      if 0 < countLimit && gi.n ≤ countLimit then do
        let c := gi.net.countSat gi.n
        if c != M then
          let src := if solutions.isSome then "--solutions" else "computed by ℰ"
          let msg := s!"the solution count M = {M} ({src}) contradicts the count {c} of \
            Network.countSat (the network of `{tp.name}` evaluated on all 2^{gi.n} inputs; \
            report §8.2)"
          IO.println (Diagnostic.at .hypothesis .solutionCountMismatch entryPos msg).toJson.compress
          return 1
        pure .kernelDecided
      else pure .hypothesis
    let cfg ← match RefConfig.ofFiles (← IO.FS.readFile "lean-toolchain")
        (← IO.FS.readFile "lake-manifest.json") with
      | .ok c => pure c
      | .error e => IO.eprintln s!"cqr certify: {e}"; return 2
    let prof ← match profile with
      | none => pure none
      | some arg => match ← loadProfile arg with
        | .ok ph => pure (some ph)
        | .error e => IO.eprintln s!"cqr certify: {e}"; return 2
    let q := CertRequest.ofInstance tp src gi M count
    let text := match sel with
      | none => renderCert q
      | some s => insertSelection (renderCert q) (renderSelection q s)
    -- the QIR text (Stage 17b: `emitQIR` can refuse a circuit; nothing is written then)
    let qirText ← match emitQIR tp.name gi.circuit with
      | .ok t => pure t
      | .error d => IO.println d.toJson.compress; return 1
    let dir := (out.getD s!"certs/{tp.name}{if sel.isSome then "_sel" else ""}").dropEndWhile
      (fun c => c == '/' || c == '\\')
    let file (n : String) : String := s!"{dir}/{n}"
    IO.FS.createDirAll dir.toString
    let certPath := file "Cert.lean"
    IO.FS.writeFile certPath text
    -- kernel check and audit (decisions 2, 3); with --bench, k + 1 runs, the first discarded
    -- Stage 21a4: with a selection, `chosen_fits` and `selected` are audited in the same run
    let selNames := if sel.isSome then
      [s!"CQRV.Cert.{q.name}.chosen_fits", s!"CQRV.Cert.{q.name}.selected"] else []
    let mut outcomes : Array (AuditOutcome × List String) := #[]
    for _ in [0:(bench.map (· + 1)).getD 1] do
      match ← checkAndAudit certPath q.theoremName with
      | .ok o =>
        let mut extra : List String := []
        for nm in selNames do
          match parseAxioms nm o.check.output with
          | some a => extra := extra ++ a
          | none => IO.eprintln s!"cqr certify: no `#print axioms {nm}` line"; return 1
        outcomes := outcomes.push (o, extra)
      | .error e => IO.eprintln s!"cqr certify: {certPath}: {e}"; return 1
    let some (last, extraAxioms) := outcomes.back? | return 1
    let timed := if bench.isSome then outcomes.toList.drop 1 else outcomes.toList
    let kernels := timed.filterMap (·.1.check.kernelMs)
    let timing : KernelTiming :=
      { wallMs := median (timed.map (·.1.check.wallMs)),
        kernelMs := if kernels.length == timed.length then some (median kernels) else none,
        runs := timed.length,
        statistic := match bench with
          | some k => s!"median of {k} (first run excluded)"
          | none => "single run" }
    let bad := (match last.result with | .pass => [] | .fail b => b) ++
      (if sel.isSome then (match auditAxioms extraAxioms with | .pass => [] | .fail b => b) else [])
    let (status, obligations) :=
      if bad.isEmpty then (Status.certified, []) else (Status.withObligations, obligationsOf bad)
    let axioms := (last.axioms ++ extraAxioms).eraseDups
    let mi ← detectMachine
    -- Stage 18b B0: a machine-detection command that hit the 20 s timeout is named on stderr;
    -- the machine fields then come from the environment (stdout unchanged).
    for c in mi.timedOut do
      IO.eprintln s!"cqr certify: machine detection: `{c}` timed out after \
        {machineCommandTimeoutMs / 1000} s; machine fields from the environment"
    let (cpu, cpus, clock) := (mi.cpu, mi.logicalCpus, mi.clock)
    let cfg := { cfg with cpu := some (cpu.getD "unknown"), logicalCpus := cpus, clock,
                          leanThreads := ← IO.getEnv "LEAN_NUM_THREADS", kernelCheck := timing }
    let base ← match Certificate.build src sig gi.entry gi.facts gi.circuit gi.circuit.grade gi.r
        gi.n M q.delta cfg feText count mode with
      | .ok c => pure c
      | .error e => IO.eprintln s!"cqr certify: {e}"; return 1
    let hw := prof.map fun (p, h) =>
      HardwareCheck.of p h base.grade base.delta base.gateCounts.total
    let cert := { base with
      proofHash := some (proofHash text cfg.lean cfg.mathlib cfg.physlib), axioms,
      status, theoremName := some q.theoremName, obligations, hardware := hw, diffusion := diff }
    let certJson := match sel with
      | none => cert.toJson
      | some s => s.addTo cert.toJson s!"CQRV.Cert.{q.name}.selected"
    -- compact, keys sorted (canonical, as `circuit_hash` and `CertifyTool sample`)
    IO.FS.writeFile (file "certificate.json") (certJson.compress ++ "\n")
    IO.FS.writeFile (file s!"{tp.name}.qir") qirText
    IO.FS.writeFile (file s!"{tp.name}.qasm") (emitQASM tp.name gi.circuit)
    let statusLine := match status, count with
      | .certified, .kernelDecided => "certified"
      | .certified, .hypothesis => s!"certified (conditional on: solution_count = {M})"
      | _, _ => s!"certificate with tracked obligations: {", ".intercalate obligations}"
    if report then
      let dif ← match (match diff with
          | .tree => diffusion gi.n none .tree mode
          | .fewLog => diffusionFew gi.n .logDepth) with
        | .ok c => pure c
        | .error d => IO.println d.toJson.compress; return 1
      let rd : RunData :=
        { name := tp.name, source := path, predicateHash := cert.predicateHash, sig,
          pattern := gi.entry.name, subst, sides, net := gi.net, oracle := gi.oracle,
          diffusion := dif, circuit := gi.circuit, n := gi.n, M, r := gi.r, delta := q.delta,
          theoremName := q.theoremName, certPath, timing,
          axioms, statusLine, certified := status == .certified,
          hardware := hw, diffusionShape := diff, count, uncompute := mode,
          extraRows := (sel.map fun s => [s.reportRow]).getD [],
          extraHeader := (sel.map fun s => [s.headerLine]).getD [] }
      IO.FS.writeFile (file "run_report.md") rd.toMarkdown
      IO.FS.writeFile (file "run_report.json") (rd.toJson.pretty ++ "\n")
    let kms := match timing.kernelMs with | some k => s!", {secs k} kernel" | none => ""
    IO.println s!"kernel check: {certPath} (exit 0, {secs timing.wallMs} wall{kms}; \
      {timing.statistic})"
    IO.println s!"axioms: {", ".intercalate axioms}"
    IO.println s!"wrote: {file "certificate.json"}, {file s!"{tp.name}.qir"}, \
      {file s!"{tp.name}.qasm"}{if report then s!", {file "run_report.md"}, \
      {file "run_report.json"}" else ""}"
    IO.println s!"front end: {feText}"
    IO.println statusLine
    if let some s := sel then IO.println s.statusLine
    if let some h := hw then IO.println h.statusLine
    return if status == .certified then 0 else 3

/-- `cqr certify <file> [--solutions M] [--iterations r] [--out dir] [--bench k] [--report]
[--profile name|path]` —
report §5.1.3, §8.4.1, §8.4.4, §9.5.1 (Stage 8b): check → extract → match → synthesize (`r = r⋆`
unless given) → front-end validation (Stage 9b) → generate `Cert.lean` → kernel check
(`lake env lean`) → axiom audit → write `certificate.json`, `<name>.qir`, `<name>.qasm` (from the
same circuit) and, with `--report`, `run_report.md` / `run_report.json` → status line.
`--bench k` repeats the kernel check `k + 1` times and records the median of the last `k`.
`--profile` (Stage 11b): the hardware check; the profile is read before anything is written.
`--shape few:log` (Stage 12d): the Grover circuit with the few-ancilla diffusion
(`groverCircuitFew … .logDepth`), certified by `grover_certificate_few_all` (Stage 13a′).
`--count-limit k` (Stage 14a): for `n ≤ k` the solution count is checked here by
`Network.countSat` (a mismatch is `solution_count_mismatch`, nothing written) and decided by the
kernel in `Cert.lean` (`hM_count`); the status line is then `certified` without condition.
`--uncompute coherent` (Stage 15b, PHASE2_SPEC.md §A.0.1): the oracle and the tree diffusion with
the adjoint uncompute, certified by `grover_certificate_coherent` (`renderCertCoherent`); `mbu`
(default) is the Phase 1 template. Stage 16b: every `Cert.lean` adds `prog`, `prog_scoped`,
`net_ok`, `front_end` (`CertRequest.progBlock`), every JSON writes `uncompute` (schema 1.8.0) and
the proved `trust_boundary.front_end`; the Stage 9b validation is no longer run. -/
def runCertify (path : String) (solutions iters : Option Nat) (out : Option String)
    (bench : Option Nat) (report : Bool) (profile : Option String)
    (diff : CertDiffusion := .tree) (countLimit : Nat := defaultCountLimit)
    (mode : UncomputeMode := .mbu) : IO UInt32 := do
  let src ← IO.FS.readFile path
  match ← frontEnd path, ← signature path solutions with
  | .error d, _ | _, .error d => IO.println d.toJson.compress; return 1
  | .ok (tp, entryPos), .ok sig =>
    let t := sig.toTerm.normalize
    let (entry, subst, sides) ← match matchLibrary library t with
      | .matched e σ ds =>
        let σs := σ.mergeSort fun a b => Term.MVar.cmp a.1 b.1 != .gt
        pure (e, ", ".intercalate (σs.map fun (m, b) => s!"{m.name} ↦ {b.toJson.compress}"),
          ds.map fun d => s!"{d.cond.render}: {d.render}")
      | r => return (← printNoMatch "certify" t r false)
    -- Stage 21a3 (PHASE2_SPEC.md §A.5 amendment (6)): the builder dispatch through the QPLP
    -- library (`CQRV.Patterns.instantiate`); the Grover arm is the unchanged `groverInstance`
    let gi ← match instantiate entry tp src sig .search iters diff countLimit mode with
      | .ok (.grover gi) => pure gi
      | .ok (.count _) =>
        IO.eprintln s!"cqr certify: matched pattern {entry.name}: a counting certificate needs \
          --problem count --precision m"
        return 2
      | .error (.diagnostic d) => IO.println d.toJson.compress; return 1
      | .error (.usage msg) => IO.eprintln s!"cqr certify: {msg}"; return 2
    certifyGrover path src tp entryPos sig subst sides gi solutions out bench report profile diff
      countLimit mode none

/-- `cqr certify <file> --budget w,d,t,a --prefer width|depth|t|anc [--solutions M] [--iterations r]
[--count-limit k] [--profile name|path] [--bench k] [--report] [--out dir]` — PHASE2_SPEC.md §A.6
amendment (8) and refinement (8′) (Stage 21a4): the front end, the signature and Algorithm 2 as
`cqr certify` (a non-match prints the proved hint); the three candidates of `candidates` through
`groverInstance` at their (shape, mode) and the request's r, with their measured grades (a builder
that fails at the instance is a candidate without a grade, not admissible); `select`. No fit: the
diagnostic `budget_unsatisfiable` (stage `synthesis`) listing every candidate's grade, exit 1,
nothing written. Otherwise the ordinary certificate path of the chosen candidate with the selection
block (`certifyGrover`); the default directory is `certs/<name>_sel`. -/
def runCertifySelect (path : String) (budget : Grade) (pref : Pref) (solutions iters : Option Nat)
    (out : Option String) (bench : Option Nat) (report : Bool) (profile : Option String)
    (countLimit : Nat) : IO UInt32 := do
  let src ← IO.FS.readFile path
  match ← frontEnd path, ← signature path solutions with
  | .error d, _ | _, .error d => IO.println d.toJson.compress; return 1
  | .ok (tp, entryPos), .ok sig =>
    let t := sig.toTerm.normalize
    let (entry, subst, sides) ← match matchLibrary library t with
      | .matched e σ ds =>
        let σs := σ.mergeSort fun a b => Term.MVar.cmp a.1 b.1 != .gt
        pure (e, ", ".intercalate (σs.map fun (m, b) => s!"{m.name} ↦ {b.toJson.compress}"),
          ds.map fun d => s!"{d.cond.render}: {d.render}")
      | r => return (← printNoMatch "certify" t r false)
    -- the three candidates at their (shape, mode) and the request's r
    let mut built : List (Candidate × Option GroverInstance) := []
    let mut firstFailure : Option Diagnostic := none
    for c in candidates do
      match instantiate entry tp src sig .search iters c.shape countLimit c.mode with
      | .ok (.grover gi) => built := built ++ [(c, some gi)]
      | .ok (.count _) =>
        IO.eprintln s!"cqr certify: matched pattern {entry.name}: a counting certificate needs \
          --problem count --precision m"
        return 2
      | .error (.usage msg) => IO.eprintln s!"cqr certify: {msg}"; return 2
      | .error (.diagnostic d) =>
        built := built ++ [(c, none)]
        if firstFailure.isNone then firstFailure := some d
    if built.all (·.2.isNone) then
      if let some d := firstFailure then IO.println d.toJson.compress
      return 1
    let results : List CandidateResult := built.map fun (c, gi?) => ⟨c, gi?.map (·.circuit.grade)⟩
    let pool : List ((Candidate × GroverInstance) × Grade) :=
      built.filterMap fun (c, gi?) => gi?.map fun gi => ((c, gi), gi.circuit.grade)
    match select budget pref pool with
    | none =>
      let msg := s!"no candidate fits the budget (w, d, t, a) = {gradeTuple budget}: " ++
        "; ".intercalate (results.map (·.text budget)) ++ " (PHASE2_SPEC §A.6 amendment (8))"
      IO.println (Diagnostic.at .synthesis .budgetUnsatisfiable entryPos msg).toJson.compress
      return 1
    | some ((c, gi), _) =>
      let info : SelectionInfo := { budget, pref, results, chosen := c }
      certifyGrover path src tp entryPos sig subst sides gi solutions out bench report profile
        c.shape countLimit c.mode (some info)

/-- Stage 21a4 — remove `--budget w,d,t,a` and `--prefer p` from the certify flags (any position);
`none` on a repeated flag. The remaining flags keep their order, so a flag list without them is
parsed exactly as before. -/
def selectionFlags : List String → Option (Option String × Option String × List String)
  | [] => some (none, none, [])
  | "--budget" :: b :: rest => do
    let (b', p, fs) ← selectionFlags rest
    if b'.isSome then none
    return (some b, p, fs)
  | "--prefer" :: p :: rest => do
    let (b, p', fs) ← selectionFlags rest
    if p'.isSome then none
    return (b, some p, fs)
  | f :: rest => (selectionFlags rest).map fun (b, p, fs) => (b, p, f :: fs)

/-- Parse `w,d,t,a`: exactly four naturals. -/
def parseBudget (s : String) : Option Grade :=
  match (s.splitOn ",").map String.toNat? with
  | [some w, some d, some t, some a] => some ⟨w, d, t, a⟩
  | _ => none

/-- `cqr certify <file> --problem count --precision m [--out dir] [--bench k] [--report]
[--count-limit k] [--uncompute mbu|coherent]` — PHASE2_SPEC.md §A.5 amendments (5)–(7) and the
refinement (5′) (Stage 21a3): the signature with `withProblem (count m)` → Algorithm 2 (a non-match
prints the proved hint, as `cqr certify`) → the dispatch `instantiate` through `qplpLibrary` → the
counting generator of `CountCert.lean` → the kernel check and the audit of `cert` (and of
`cert_count` when the count is decided; one Lean run) → `certificate.json` (schema 1.10.0, pattern
Count), `<name>.qir`, `<name>.qasm` and, with `--report`, the counting run report, whose matching
rows come from the actual match. For `n ≤ --count-limit` the count is decided by `Network.countSat`
and M = 0 is refused before anything is written (diagnostic `no_solutions`, exit 1); for
`n > --count-limit` the certificate is `cert` only, `instance.M` is null, `solution_count` is
`not_decided` and ε is the maximum over a, π/2^m + π²/4^m (5′). `--bench k`: `k + 1` kernel checks,
the median of the last `k`, as `cqr certify`. The default directory is `certs/<name>_count`. -/
def runCertifyCount (path : String) (m : Nat) (out : Option String) (bench : Option Nat)
    (report : Bool) (countLimit : Nat) (mode : UncomputeMode) : IO UInt32 := do
  let src ← IO.FS.readFile path
  match ← frontEnd path, ← signature path none with
  | .error d, _ | _, .error d => IO.println d.toJson.compress; return 1
  | .ok (tp, entryPos), .ok sig =>
    let t := (sig.withProblem (.count m)).toTerm.normalize
    let (entry, subst, sides) ← match matchLibrary library t with
      | .matched e σ ds =>
        let σs := σ.mergeSort fun a b => Term.MVar.cmp a.1 b.1 != .gt
        pure (e, ", ".intercalate (σs.map fun (m, b) => s!"{m.name} ↦ {b.toJson.compress}"),
          ds.map fun d => s!"{d.cond.render}: {d.render}")
      | r => return (← printNoMatch "certify" t r false)
    let q ← match instantiate entry tp src sig (.count m) none .tree countLimit mode with
      | .ok (.count q) => pure q
      | .ok (.grover _) =>
        IO.eprintln s!"cqr certify: matched pattern {entry.name} is a search pattern; a counting \
          request matches Count"
        return 2
      | .error (.diagnostic d) => IO.println d.toJson.compress; return 1
      | .error (.usage msg) => IO.eprintln s!"cqr certify: {msg}"; return 2
    -- amendment (5): a decided count of 0 is refused before anything is written
    if q.M == some 0 then
      IO.println (Diagnostic.at .hypothesis .noSolutions entryPos s!"the predicate of `{tp.name}` \
        has no satisfying assignment (Network.countSat on all 2^{q.n} inputs is 0): the counting \
        certificate makes no claim for M = 0 (PHASE2_SPEC §A.4, §A.5 amendment (5))").toJson.compress
      return 1
    let cfg ← match RefConfig.ofFiles (← IO.FS.readFile "lean-toolchain")
        (← IO.FS.readFile "lake-manifest.json") with
      | .ok c => pure c
      | .error e => IO.eprintln s!"cqr certify: {e}"; return 2
    let text := renderCountCert q
    let qirText ← match emitQIR tp.name q.circuit with
      | .ok t => pure t
      | .error d => IO.println d.toJson.compress; return 1
    let dir := (out.getD s!"certs/{tp.name}_count").dropEndWhile (fun c => c == '/' || c == '\\')
    let file (n : String) : String := s!"{dir}/{n}"
    IO.FS.createDirAll dir.toString
    let certPath := file "Cert.lean"
    IO.FS.writeFile certPath text
    -- the kernel check and the audit of `cert` and (decided count) `cert_count`, one Lean run;
    -- with --bench, k + 1 runs, the first discarded
    let mut outcomes : Array (AuditOutcome × List String) := #[]
    for _ in [0:(bench.map (· + 1)).getD 1] do
      match ← checkAndAudit certPath q.theoremName with
      | .ok o =>
        let axsCount ← if q.M.isSome then
            match parseAxioms q.countTheoremName o.check.output with
            | some a => pure a
            | none =>
              IO.eprintln s!"cqr certify: no `#print axioms {q.countTheoremName}` line"; return 1
          else pure []
        outcomes := outcomes.push (o, axsCount)
      | .error e => IO.eprintln s!"cqr certify: {certPath}: {e}"; return 1
    let some (last, axsCount) := outcomes.back? | return 1
    let timed := if bench.isSome then outcomes.toList.drop 1 else outcomes.toList
    let kernels := timed.filterMap (·.1.check.kernelMs)
    let timing : KernelTiming :=
      { wallMs := median (timed.map (·.1.check.wallMs)),
        kernelMs := if kernels.length == timed.length then some (median kernels) else none,
        runs := timed.length,
        statistic := match bench with
          | some k => s!"median of {k} (first run excluded)"
          | none => "single run" }
    let bad := (match last.result with | .pass => [] | .fail b => b) ++
      (if q.M.isSome then (match auditAxioms axsCount with | .pass => [] | .fail b => b) else [])
    let obligations := obligationsOf bad
    let status := if bad.isEmpty then Status.certified else Status.withObligations
    let mi ← detectMachine
    for c in mi.timedOut do
      IO.eprintln s!"cqr certify: machine detection: `{c}` timed out after \
        {machineCommandTimeoutMs / 1000} s; machine fields from the environment"
    let cfg := { cfg with cpu := some (mi.cpu.getD "unknown"), logicalCpus := mi.logicalCpus,
                          clock := mi.clock, leanThreads := ← IO.getEnv "LEAN_NUM_THREADS",
                          kernelCheck := timing }
    let axioms := (last.axioms ++ axsCount).eraseDups
    let cert := { CountCertificate.ofRequest q cfg with
      proofHash := some (proofHash text cfg.lean cfg.mathlib cfg.physlib), axioms, status,
      theoremName := some q.theoremName, obligations }
    IO.FS.writeFile (file "certificate.json") (cert.toJson.compress ++ "\n")
    IO.FS.writeFile (file s!"{tp.name}.qir") qirText
    IO.FS.writeFile (file s!"{tp.name}.qasm") (emitQASM tp.name q.circuit)
    let statusLine := countStatusLine q status obligations
    if report then
      let rd : CountRunData :=
        { q, source := path, pattern := entry.name, subst, sides, certPath, timing, axioms,
          statusLine, certified := status == .certified }
      IO.FS.writeFile (file "run_report.md") rd.toMarkdown
      IO.FS.writeFile (file "run_report.json") (rd.toJson.pretty ++ "\n")
    let kms := match timing.kernelMs with | some k => s!", {secs k} kernel" | none => ""
    IO.println s!"kernel check: {certPath} (exit 0, {secs timing.wallMs} wall{kms}; \
      {timing.statistic})"
    IO.println s!"axioms: {", ".intercalate axioms}"
    IO.println s!"wrote: {file "certificate.json"}, {file s!"{tp.name}.qir"}, \
      {file s!"{tp.name}.qasm"}{if report then s!", {file "run_report.md"}, \
      {file "run_report.json"}" else ""}"
    IO.println s!"front end: {frontEndProvedText}"
    IO.println statusLine
    return if status == .certified then 0 else 3

/-- Stage 21a3 — remove `--problem search|count` and `--precision m` from the certify flags
(any position); `none` on an unknown value or a repeated flag. The remaining flags keep their
order, so a flag list without them is parsed exactly as before. -/
def certifyRequest : List String → Option (Option String × Option Nat × List String)
  | [] => some (none, none, [])
  | "--problem" :: p :: rest => do
    if p != "search" && p != "count" then none
    let (q, m, fs) ← certifyRequest rest
    if q.isSome then none
    return (some p, m, fs)
  | "--precision" :: k :: rest => do
    let m ← k.toNat?
    let (q, m', fs) ← certifyRequest rest
    if m'.isSome then none
    return (q, some m, fs)
  | f :: rest => (certifyRequest rest).map fun (q, m, fs) => (q, m, f :: fs)

/-- PHASE2_SPEC §C.1 (Stage 24a) — `cqr hw capabilities <target.json>`: the name, the three
capability flags with their sources, the uncomputation modes the target supports (`mbu` needs
mid-circuit measurement and feed forward; `coherent` needs neither), and the snapshot hash check
(Lean's SHA3-256 of the canonical `calibration` against `snapshot.hash`): `snapshot hash ok`
and exit 0, or the mismatch and exit 1. A missing, unreadable or malformed target: message,
exit 2. -/
def runHwCapabilities (path : String) : IO UInt32 := do
  match ← Hardware.readTarget path with
  | .error msg => IO.eprintln s!"cqr hw capabilities: {msg}"; return 2
  | .ok t =>
    IO.println s!"name: {t.name}"
    IO.println s!"num_qubits: {t.numQubits}"
    let flag (k : String) (c : Hardware.Capability) : IO Unit :=
      IO.println s!"{k}: {c.value} (source: {c.source})"
    flag "mid_circuit_measurement" t.capabilities.midCircuitMeasurement
    flag "feed_forward" t.capabilities.feedForward
    flag "reset" t.capabilities.reset
    IO.println s!"uncompute modes: {", ".intercalate t.uncomputeModes}"
    let computed := t.calibrationHash
    if computed == t.snapshotHash then
      IO.println "snapshot hash ok"
      return 0
    else
      IO.println s!"snapshot hash mismatch: file {t.snapshotHash}, computed {computed}"
      return 1

/-- PHASE2_SPEC §C.3 (Stage 26c1b, L4) — `cqr hw check --artifact <dir> --target <target.json>
[--out <dir>]`: reads the artifact's `logical.json`, `witness.json`, `physical.json` and
`manifest.json`, re-checks the three hashes (the logical circuit — through the file and the Lean
literal's own `circuitHash` —, the witness, the target snapshot), compacts the witness and the
physical circuit through the manifest's `used_qubits`, and writes
`<out>/<instance>__<target>/Check.lean` (default `examples/hw_checks`): the literals and the
kernel-checked theorems (`recon`, `phys_wf`, `phys_nBits`, `c_wf`, `edges_ok`, `init_eq`,
`phys_channel`, `phys_zero`), two tampering theorems and the `#print axioms` lines. The file is
checked with `lake env lean`, as the certificates are. Exit 0; a hash mismatch or a malformed file:
message, exit 1; an unreadable file: exit 2. -/
def runHwCheck (artifactDir target : String) (out : String) : IO UInt32 := do
  let read (f : String) : IO (Option String) := do
    try return some (← IO.FS.readFile (System.FilePath.mk artifactDir / f).toString)
    catch _ => return none
  let some manifest ← read "manifest.json" | do IO.eprintln s!"cqr hw check: {artifactDir}/manifest.json unreadable"; return 2
  let some logical ← read "logical.json" | do IO.eprintln s!"cqr hw check: {artifactDir}/logical.json unreadable"; return 2
  let some witness ← read "witness.json" | do IO.eprintln s!"cqr hw check: {artifactDir}/witness.json unreadable"; return 2
  let some physical ← read "physical.json" | do IO.eprintln s!"cqr hw check: {artifactDir}/physical.json unreadable"; return 2
  match ← Hardware.readTarget target with
  | .error msg => IO.eprintln s!"cqr hw check: {msg}"; return 2
  | .ok t =>
    match Hardware.generateCheck manifest logical witness physical t target with
    | .error msg => IO.eprintln s!"cqr hw check: {msg}"; return 1
    | .ok (text, r) =>
      let dir := System.FilePath.mk out / r.name
      IO.FS.createDirAll dir
      IO.FS.writeFile (dir / "Check.lean") text
      IO.println s!"{r.name}: hashes ok; {r.gates} logical gates, {r.order} order entries, \
        {r.physical} physical gates on {r.usedQubits} qubits; wrote {(dir / "Check.lean").toString}"
      return 0

/-- The artifact data `cqr hw grade` / `cqr hw certify` read: the manifest's basis, used qubits,
data positions and Grover parameters, and the physical circuit compacted. -/
structure ArtifactData where
  manifest : Hardware.ManifestData
  dataPhys : List Nat
  delta : Rat
  G : List Hardware.BasisGate
  deviceWidth : Nat

def readArtifactData (artifactDir : String) : IO (Except String ArtifactData) := do
  let read (f : String) : IO (Option String) := do
    try return some (← IO.FS.readFile (System.FilePath.mk artifactDir / f).toString)
    catch _ => return none
  let some manifest ← read "manifest.json" | return .error s!"{artifactDir}/manifest.json unreadable"
  let some physical ← read "physical.json" | return .error s!"{artifactDir}/physical.json unreadable"
  return do
    let mj ← Lean.Json.parse manifest
    let m ← Hardware.manifestOfJson mj
    let layout ← Hardware.field "manifest" mj "layout"
    let dataPhys ← Hardware.natList "manifest.layout.data_physical" (← Hardware.field "manifest.layout" layout "data_physical")
    let deviceWidth ← Hardware.natField "manifest" mj "device_width"
    let delta ← match mj.getObjVal? "grover" with
      | .ok (.null) => pure (0 : Rat)
      | .ok gj =>
        let n ← Hardware.natField "manifest.grover" gj "n"
        let r ← Hardware.natField "manifest.grover" gj "r"
        let M ← Hardware.natField "manifest.grover" gj "M"
        pure (Certify.groverDelta r n M)
      | .error _ => pure (0 : Rat)
    let pj ← Lean.Json.parse physical
    let G ← Hardware.physOfJson m.usedQubits pj
    return { manifest := m, dataPhys, delta, G, deviceWidth }

/-- PHASE2_SPEC §C.3 (Stage 26c2, P1) — `cqr hw grade --artifact <dir> --target <target.json>
--ff-latency <ns> [--json]`: the physical grade of the artifact's physical circuit on the target at
the feed-forward latency `L` (ns, a decimal): the qubits used, the two-qubit count, the mid-circuit
measurements, the feed-forward count, the exact wall-clock depth (ASAP), the exact physical bound
(25a's `physical_bound`) and whether it is vacuous. `--json`: the canonical JSON `hw/physgrade.py`
prints. Exit 0; a missing duration or rate, or a malformed file: message, exit 1; unreadable: 2. -/
def runHwGrade (artifactDir target lat : String) (json : Bool) : IO UInt32 := do
  let some L := Hardware.parseDecimalSci lat | IO.eprintln s!"cqr hw grade: --ff-latency {lat} is not a decimal"; return 2
  match ← readArtifactData artifactDir with
  | .error msg => IO.eprintln s!"cqr hw grade: {msg}"; return 2
  | .ok a =>
    match ← Hardware.readTarget target with
    | .error msg => IO.eprintln s!"cqr hw grade: {msg}"; return 2
    | .ok t =>
      match Hardware.physGradeOf t a.manifest.basis a.manifest.usedQubits a.G L a.dataPhys a.delta with
      | .error msg => IO.eprintln s!"cqr hw grade: {msg}"; return 1
      | .ok g =>
        if json then
          IO.println (g.toJson L).compress
        else
          IO.println s!"{a.manifest.instance_} on {t.name}, feed-forward latency {Hardware.ratStr L} ns (an assumption, not a property of the device)"
          IO.println s!"qubits: {g.qubits}"
          IO.println s!"two_qubit: {g.twoQubit}"
          IO.println s!"mid_measurements: {g.midMeas}"
          IO.println s!"feed_forward: {g.feedForward}"
          IO.println s!"depth_ns: {Hardware.ratStr g.depth} (≈ {Hardware.ratFloat g.depth})"
          IO.println s!"bound: {Hardware.ratStr g.bound} (≈ {Hardware.ratFloat g.bound}){if g.vacuous then " VACUOUS (≥ 1)" else ""}"
          IO.println "reported, not certified: the bound is a sum of calibrated rates (Stage 27 is the noise theorem)"
        return 0

/-- PHASE2_SPEC §C.4 (4) (Stage 27b, B2) — `cqr hw noise --artifact <dir> --target <target.json>
[--json]`: the conditional noise bound `δ' = δ + Σ p_g + Σ r_j` of the artifact's physical circuit on
the target under (P-stoch) (the Pauli reading `p = min 1 ((d+1)/d · r)`; virtual `rz` has `p = 0`) and
(P-ro) (`p = r` for measurements and the data readouts), exact, with the clamp flag and the vacuity,
beside 25a's `p = r` figure. `--json`: the canonical JSON `hw/noisebound.py` prints. Conditional on
the premises; never a fact about a device. -/
def runHwNoise (artifactDir target : String) (json : Bool) : IO UInt32 := do
  match ← readArtifactData artifactDir with
  | .error msg => IO.eprintln s!"cqr hw noise: {msg}"; return 2
  | .ok a =>
    match ← Hardware.readTarget target with
    | .error msg => IO.eprintln s!"cqr hw noise: {msg}"; return 2
    | .ok t =>
      match Hardware.physGradeOf t a.manifest.basis a.manifest.usedQubits a.G 0 a.dataPhys a.delta,
          Hardware.noiseBoundOf t a.manifest.usedQubits a.G a.dataPhys a.delta with
      | .error msg, _ | _, .error msg => IO.eprintln s!"cqr hw noise: {msg}"; return 1
      | .ok g, .ok nb =>
        if json then
          IO.println (nb.toJson g.bound).compress
        else
          IO.println s!"{a.manifest.instance_} on {t.name}: conditional noise bound under (P-stoch), (P-ro), (P-idle), (P-cal)"
          IO.println s!"noise_bound: {Hardware.ratStr nb.bound} (≈ {Hardware.ratFloat nb.bound}){if nb.vacuous then " VACUOUS (≥ 1)" else ""}{if nb.clamped then "; some p clamped to 1" else ""}"
          IO.println s!"physical_bound_p_eq_r (25a): {Hardware.ratStr g.bound} (≈ {Hardware.ratFloat g.bound})"
          IO.println "conditional on the premises, which are assumptions about the device, not facts proved here; not verified on hardware"
        return 0

def hwNoiseFlags : List String → Option (Option String × Option String × Bool)
  | [] => some (none, none, false)
  | "--artifact" :: d :: rest => do let (_, t, j) ← hwNoiseFlags rest; return (some d, t, j)
  | "--target" :: t :: rest => do let (d, _, j) ← hwNoiseFlags rest; return (d, some t, j)
  | "--json" :: rest => do let (d, t, _) ← hwNoiseFlags rest; return (d, t, true)
  | _ => none

/-- `--artifact d`, `--target t`, `--ff-latency l`, `--json` of `cqr hw grade`, in any position. -/
def hwGradeFlags : List String → Option (Option String × Option String × Option String × Bool)
  | [] => some (none, none, none, false)
  | "--artifact" :: d :: rest => do
    let (_, t, l, j) ← hwGradeFlags rest
    return (some d, t, l, j)
  | "--target" :: t :: rest => do
    let (d, _, l, j) ← hwGradeFlags rest
    return (d, some t, l, j)
  | "--ff-latency" :: l :: rest => do
    let (d, t, _, j) ← hwGradeFlags rest
    return (d, t, some l, j)
  | "--json" :: rest => do
    let (d, t, l, _) ← hwGradeFlags rest
    return (d, t, l, true)
  | _ => none

/-- PHASE2_SPEC §C.3 (Stage 26c2, P2) — `cqr hw certify --cert <dir> --artifact <dir> --target
<target.json> --ff-latency <ns> [--out <dir>]`: the physical certificate of a committed logical
certificate on a target, from the artifact: `PhysCert.lean` (self-contained: the logical
certificate's body verbatim, the artifact's literals and theorems, `emitted = C` by the kernel,
`RealizesExact` transferred to the physical circuit, `PhysGrade` at L = 0 and at the latency given),
`physical.qasm` (printed from the validated physical circuit) and `manifest.json` (the hashes, the
grades, the status words). The default output is `examples/certs/<cert>_<target without fake_>/`.
Exit 0; a hash mismatch or a malformed file 1; an unreadable file 2. -/
def runHwCertify (certDir artifactDir target lat : String) (out : Option String) : IO UInt32 := do
  let some L := Hardware.parseDecimalSci lat | IO.eprintln s!"cqr hw certify: --ff-latency {lat} is not a decimal"; return 2
  let read (dir f : String) : IO (Option String) := do
    try return some (← IO.FS.readFile (System.FilePath.mk dir / f).toString)
    catch _ => return none
  let some certLean ← read certDir "Cert.lean" | IO.eprintln s!"cqr hw certify: {certDir}/Cert.lean unreadable"; return 2
  let some certJson ← read certDir "certificate.json" | IO.eprintln s!"cqr hw certify: {certDir}/certificate.json unreadable"; return 2
  let some manifest ← read artifactDir "manifest.json" | IO.eprintln s!"cqr hw certify: {artifactDir}/manifest.json unreadable"; return 2
  let some logical ← read artifactDir "logical.json" | IO.eprintln s!"cqr hw certify: {artifactDir}/logical.json unreadable"; return 2
  let some witness ← read artifactDir "witness.json" | IO.eprintln s!"cqr hw certify: {artifactDir}/witness.json unreadable"; return 2
  let some physical ← read artifactDir "physical.json" | IO.eprintln s!"cqr hw certify: {artifactDir}/physical.json unreadable"; return 2
  let some targetText ← (do try return some (← IO.FS.readFile target) catch _ => return none)
    | IO.eprintln s!"cqr hw certify: {target} unreadable"; return 2
  match ← readArtifactData artifactDir with
  | .error msg => IO.eprintln s!"cqr hw certify: {msg}"; return 2
  | .ok a =>
    match ← Hardware.readTarget target with
    | .error msg => IO.eprintln s!"cqr hw certify: {msg}"; return 2
    | .ok t =>
      let certBase := (System.FilePath.mk certDir).fileName.getD "cert"
      let targetShort := if t.name.startsWith "fake_" then t.name.drop 5 else t.name
      let certName := s!"{certBase}_{targetShort}"
      let artName := s!"{a.manifest.instance_}__{a.manifest.target}"
      let runText ← read "docs/hw_runs" s!"{artName}.json"
      let nBits := (a.G.filter Hardware.BasisGate.isMeasure).length
      match Hardware.generatePhysCert certName certBase certLean certJson manifest logical witness physical t target targetText L
          a.deviceWidth a.dataPhys nBits runText with
      | .error msg => IO.eprintln s!"cqr hw certify: {msg}"; return 1
      | .ok (lean, qasm, man, grades) =>
        let dir := System.FilePath.mk (out.getD s!"examples/certs/{certName}")
        IO.FS.createDirAll dir
        IO.FS.writeFile (dir / "PhysCert.lean") lean
        IO.FS.writeFile (dir / "physical.qasm") qasm
        IO.FS.writeFile (dir / "manifest.json") (man ++ "\n")
        for (l, g) in grades do
          IO.println s!"L = {Hardware.ratStr l} ns: qubits {g.qubits}, two-qubit {g.twoQubit}, mid-circuit {g.midMeas}, \
            feed-forward {g.feedForward}, depth {Hardware.ratStr g.depth} ns (≈ {Hardware.ratFloat g.depth}), \
            bound {Hardware.ratStr g.bound} (≈ {Hardware.ratFloat g.bound}){if g.vacuous then " VACUOUS" else ""}"
        IO.println s!"{certName}: hashes ok; wrote {dir.toString}/PhysCert.lean, physical.qasm, manifest.json \
          (check PhysCert.lean with `lake env lean`; reported, not certified: the noise theorem is Stage 27)"
        return 0

/-- PHASE2_SPEC §C.4 (4) (Stage 27b2, B4) — `cqr hw noisecert --artifact <dir> --target <target.json>
--ff-latency <ns> [--cert <dir>] [--out <dir>]`: the conditional certificate. With `--cert`: 26c2's
physical certificate plus the noise block (`phys_noisy_inst`), `PhysCert.lean`; without: the channel
form of the bare MBU gadget (`gadget_noisy`), `NoiseCert.lean`. Both: `physical.qasm` and
`manifest.json` with `noise_conditional`, the four premises, the meaning sentence and the emulator
comparison at δ' from the recorded run (`docs/hw_runs/<artifact>.json`; "no run recorded for this
artifact" otherwise). Default output `examples/certs/<cert or instance>_<target without fake_>/`. -/
def runHwNoiseCert (artifactDir target lat : String) (certDir : Option String) (out : Option String) : IO UInt32 := do
  let some L := Hardware.parseDecimalSci lat | IO.eprintln s!"cqr hw noisecert: --ff-latency {lat} is not a decimal"; return 2
  let read (dir f : String) : IO (Option String) := do
    try return some (← IO.FS.readFile (System.FilePath.mk dir / f).toString)
    catch _ => return none
  let some manifest ← read artifactDir "manifest.json" | IO.eprintln s!"cqr hw noisecert: {artifactDir}/manifest.json unreadable"; return 2
  let some logical ← read artifactDir "logical.json" | IO.eprintln s!"cqr hw noisecert: {artifactDir}/logical.json unreadable"; return 2
  let some witness ← read artifactDir "witness.json" | IO.eprintln s!"cqr hw noisecert: {artifactDir}/witness.json unreadable"; return 2
  let some physical ← read artifactDir "physical.json" | IO.eprintln s!"cqr hw noisecert: {artifactDir}/physical.json unreadable"; return 2
  let some targetText ← (do try return some (← IO.FS.readFile target) catch _ => return none)
    | IO.eprintln s!"cqr hw noisecert: {target} unreadable"; return 2
  match ← readArtifactData artifactDir with
  | .error msg => IO.eprintln s!"cqr hw noisecert: {msg}"; return 2
  | .ok a =>
    match ← Hardware.readTarget target with
    | .error msg => IO.eprintln s!"cqr hw noisecert: {msg}"; return 2
    | .ok t =>
      let targetShort := if t.name.startsWith "fake_" then t.name.drop 5 else t.name
      let artName := s!"{a.manifest.instance_}__{a.manifest.target}"
      let runFile := s!"docs/hw_runs/{artName}.json"
      let runText ← read "docs/hw_runs" s!"{artName}.json"
      let nBits := (a.G.filter Hardware.BasisGate.isMeasure).length
      let result ← match certDir with
        | some cd => do
          match ← read cd "Cert.lean", ← read cd "certificate.json" with
          | some certLean, some certJson =>
            let certBase := (System.FilePath.mk cd).fileName.getD "cert"
            let certName := s!"{certBase}_{targetShort}"
            pure (Hardware.generateNoiseCert certName certBase certLean certJson manifest logical witness physical t target
              targetText L a.deviceWidth a.dataPhys nBits runText runFile |>.map fun r => (certName, "PhysCert.lean", certBase, r))
          | _, _ => pure (.error s!"{cd}/Cert.lean or certificate.json unreadable")
        | none =>
          let certName := s!"{a.manifest.instance_}_{targetShort}"
          pure (Hardware.generateGadgetNoiseCert certName manifest logical witness physical t target targetText
            a.deviceWidth a.dataPhys nBits runText runFile |>.map fun r => (certName, "NoiseCert.lean", "", r))
      match result with
      | .error msg => IO.eprintln s!"cqr hw noisecert: {msg}"; return 1
      | .ok (certName, leanFile, _, lean, qasm, man, nd, emu) =>
        let dir := System.FilePath.mk (out.getD s!"examples/certs/{certName}")
        IO.FS.createDirAll dir
        IO.FS.writeFile (dir / leanFile) lean
        IO.FS.writeFile (dir / "physical.qasm") qasm
        IO.FS.writeFile (dir / "manifest.json") (man ++ "\n")
        IO.println s!"{certName}: noise_bound {Hardware.ratStr nd.nb.bound} (≈ {Hardware.ratFloat nd.nb.bound}){if nd.nb.vacuous then " VACUOUS" else ""}{if nd.nb.clamped then ", clamped" else ""}; 25a's p = r bound {Hardware.ratStr nd.physBound} (≈ {Hardware.ratFloat nd.physBound})"
        match emu with
        | some e => IO.println s!"emulator comparison ({runFile}): p_hat {Hardware.ratStr e.pHat} vs threshold at delta_prime {Hardware.ratFloat e.thresholdNew} → {if e.passes then "passes" else "fails"} (a sanity check: the emulator's noise is not of the (P-stoch) form)"
        | none => IO.println "emulator comparison: no run recorded for this artifact"
        IO.println s!"wrote {dir.toString}/{leanFile}, physical.qasm, manifest.json (check {leanFile} with `lake env lean`); conditional on the premises P-cal, P-stoch, P-ro, P-idle; not verified on hardware"
        return 0

/-- The flags of `cqr hw noisecert`, in any position. -/
def hwNoiseCertFlags : List String →
    Option (Option String × Option String × Option String × Option String × Option String)
  | [] => some (none, none, none, none, none)
  | "--artifact" :: a :: rest => do let (_, t, l, c, o) ← hwNoiseCertFlags rest; return (some a, t, l, c, o)
  | "--target" :: t :: rest => do let (a, _, l, c, o) ← hwNoiseCertFlags rest; return (a, some t, l, c, o)
  | "--ff-latency" :: l :: rest => do let (a, t, _, c, o) ← hwNoiseCertFlags rest; return (a, t, some l, c, o)
  | "--cert" :: c :: rest => do let (a, t, l, _, o) ← hwNoiseCertFlags rest; return (a, t, l, some c, o)
  | "--out" :: o :: rest => do let (a, t, l, c, _) ← hwNoiseCertFlags rest; return (a, t, l, c, some o)
  | _ => none

/-- The flags of `cqr hw certify`, in any position. -/
def hwCertifyFlags : List String →
    Option (Option String × Option String × Option String × Option String × Option String)
  | [] => some (none, none, none, none, none)
  | "--cert" :: c :: rest => do
    let (_, a, t, l, o) ← hwCertifyFlags rest
    return (some c, a, t, l, o)
  | "--artifact" :: a :: rest => do
    let (c, _, t, l, o) ← hwCertifyFlags rest
    return (c, some a, t, l, o)
  | "--target" :: t :: rest => do
    let (c, a, _, l, o) ← hwCertifyFlags rest
    return (c, a, some t, l, o)
  | "--ff-latency" :: l :: rest => do
    let (c, a, t, _, o) ← hwCertifyFlags rest
    return (c, a, t, some l, o)
  | "--out" :: o :: rest => do
    let (c, a, t, l, _) ← hwCertifyFlags rest
    return (c, a, t, l, some o)
  | _ => none

/-- The candidates of a request on a target: the artifacts `hw/artifacts/<request>_*__<target>/`. -/
def selCandidates (request targetName : String) (t : Hardware.HardwareTarget) :
    IO (Except String (List Hardware.SelCand)) := do
  let root := System.FilePath.mk "hw" / "artifacts"
  let entries ← root.readDir
  let names := (entries.map (·.fileName)).toList.filter fun d =>
    d.startsWith (request ++ "_") && d.endsWith ("__" ++ targetName)
  let names := names.mergeSort
  let rates := Hardware.RateTable.ofCalibration t.calibration
  match rates with
  | .error msg => return .error msg
  | .ok rates =>
    let mut out : List Hardware.SelCand := []
    for d in names do
      match ← readArtifactData (root / d).toString with
      | .error msg => return .error msg
      | .ok a =>
        let some physical ← (do try return some (← IO.FS.readFile (root / d / "physical.json").toString) catch _ => return none)
          | return .error s!"{d}/physical.json unreadable"
        let physHash := match Lean.Json.parse physical with
          | .ok pj => Certify.SHA3.sha3String pj.compress
          | .error _ => ""
        out := out ++ [{ name := d, mbu := a.manifest.uncompute == "mbu", basis := a.manifest.basis, G := a.G,
                         dev := a.manifest.usedQubits, dataPhys := a.dataPhys, delta := a.delta, physHash,
                         durs := t.durations.restrict a.manifest.usedQubits,
                         rates := rates.restrict a.manifest.usedQubits }]
    return .ok out

/-- The noise candidates of a selection (Stage 27b, B2): each candidate with its conditional noise
bound (`noiseBound`) beside its grade. -/
def noiseCands (cs : List Hardware.SelCand) (L : Rat) : Except String (List Hardware.NoiseCand) := do
  let gs ← Hardware.gradeCands cs L
  gs.mapM fun (c, g) => do
    let nb ← Hardware.noiseBound c.rates c.dev c.G c.dataPhys c.delta
    return ⟨⟨c.name, c.mbu, g⟩, nb.bound, nb.clamped⟩

/-- The `noise` row of the choice table. -/
def noiseRow (ff : Bool) (budget : Option Rat) (cs : List Hardware.SelCand) : Except String String := do
  let ncs ← noiseCands cs 0
  let choice := Hardware.selectNoise ff budget ncs
  let all := ", ".intercalate (ncs.map fun c =>
    s!"{c.cand.name}: {Hardware.ratStr c.noise}{if c.clamped then " (clamped)" else ""}")
  return s!"noise: {match choice with
    | some c => s!"{c.cand.name} ({Hardware.ratStr c.noise})"
    | none => "none (no admissible candidate)"} [{all}]"

/-- PHASE2_SPEC §C.3 (Stage 26c2b, P4) — `cqr hw select --request <name> --target <target.json>
--prefer twoq|depth|bound|noise [--ff-latency <ns>] [--budget X] [--out <dir>] [--table]`: the request's
committed artifacts on the target are the candidates; each is graded (`PhysGrade` at the latency,
default 0) and `selectPhys` chooses the first minimal admissible one (mbu needs the target's
feed-forward; the budget, if given, bounds the component). Writes
`<out>/<request>__<target>/Select.lean` (default `examples/hw_select`), where the kernel re-decides
every grade and the choice; prints the choice (or `none`, the honest answer). `--table`: the choice
under every preference (twoq; depth at L = 0 and 1000; bound; noise), no file. `--prefer noise` (Stage 27b, B2)
selects by the conditional noise bound (`selectNoise`) and writes no file. -/
def runHwSelect (request target pref : String) (lat : Option String) (budget : Option String)
    (out : Option String) (table : Bool) : IO UInt32 := do
  let isNoise := pref == "noise"
  let some p := (if isNoise then some Hardware.PhysPref.bound else Hardware.PhysPref.parse? pref)
    | IO.eprintln s!"cqr hw select: --prefer {pref}"; return 2
  let some L := Hardware.parseDecimalSci (lat.getD "0") | IO.eprintln s!"cqr hw select: --ff-latency {lat.getD ""} is not a decimal"; return 2
  let budgetR ← match budget with
    | none => pure (none : Option Rat)
    | some b => match Hardware.parseDecimalSci b with
      | some q => pure (some q)
      | none => IO.eprintln s!"cqr hw select: --budget {b} is not a decimal"; return 2
  match ← Hardware.readTarget target with
  | .error msg => IO.eprintln s!"cqr hw select: {msg}"; return 2
  | .ok t =>
    let targetName := ((System.FilePath.mk target).fileStem).getD t.name
    match ← selCandidates request targetName t with
    | .error msg => IO.eprintln s!"cqr hw select: {msg}"; return 1
    | .ok cs =>
      if cs.isEmpty then IO.eprintln s!"cqr hw select: no artifact of {request} on {targetName}"; return 1
      let ff := t.capabilities.feedForward.value
      if table then
        for (pp, l) in [(Hardware.PhysPref.twoq, (0 : Rat)), (.depth, 0), (.depth, 1000), (.bound, 0)] do
          match Hardware.choiceRow pp l ff budgetR cs with
          | .error msg => IO.eprintln s!"cqr hw select: {msg}"; return 1
          | .ok row => IO.println row
        match noiseRow ff budgetR cs with
        | .error msg => IO.eprintln s!"cqr hw select: {msg}"; return 1
        | .ok row => IO.println row
        return 0
      if isNoise then
        -- Stage 27b (B2): the `noise` preference selects by the conditional noise bound (`selectNoise`);
        -- it writes no file — the committed `Select.lean` files are the grade preferences'
        match noiseCands cs L with
        | .error msg => IO.eprintln s!"cqr hw select: {msg}"; return 1
        | .ok ncs =>
          let name := s!"{request}__{targetName}"
          match Hardware.selectNoise ff budgetR ncs with
          | some c => IO.println s!"{name}: noise → {c.cand.name} (noise_bound {Hardware.ratStr c.noise} ≈ {Hardware.ratFloat c.noise}{if c.clamped then ", clamped" else ""}); conditional on the premises (P-stoch), (P-ro), (P-idle), (P-cal); no file written"
          | none => IO.println s!"{name}: noise → none: no admissible candidate\
              {match budgetR with | some b => s!" within the budget {Hardware.ratStr b}" | none => ""} (the honest answer); no file written"
          return 0
      match Hardware.gradeCands cs L with
      | .error msg => IO.eprintln s!"cqr hw select: {msg}"; return 1
      | .ok gs =>
        let choice := Hardware.selectPhys ff budgetR p (Hardware.toPhysCands gs)
        let name := s!"{request}__{targetName}"
        let text := Hardware.selectFile name request t.name s!"hw/targets/{targetName}.json" ff p L budgetR gs choice
        let dir := System.FilePath.mk (out.getD "examples/hw_select") / name
        IO.FS.createDirAll dir
        IO.FS.writeFile (dir / "Select.lean") text
        match choice with
        | some c => IO.println s!"{name}: {pref} at L = {Hardware.ratStr L} ns → {c.name} ({(c.toJson L).compress}); wrote {(dir / "Select.lean").toString}"
        | none => IO.println s!"{name}: {pref} at L = {Hardware.ratStr L} ns → none: no admissible candidate\
            {match budgetR with | some b => s!" within the budget {Hardware.ratStr b}" | none => ""} (the honest answer); wrote {(dir / "Select.lean").toString}"
        return 0

/-- The flags of `cqr hw select`, in any position. -/
structure HwSelectFlags where
  request : Option String := none
  target : Option String := none
  prefer : Option String := none
  lat : Option String := none
  budget : Option String := none
  out : Option String := none
  table : Bool := false

def hwSelectFlags : List String → Option HwSelectFlags
  | [] => some {}
  | "--request" :: r :: rest => do let f ← hwSelectFlags rest; return { f with request := some r }
  | "--target" :: t :: rest => do let f ← hwSelectFlags rest; return { f with target := some t }
  | "--prefer" :: p :: rest => do let f ← hwSelectFlags rest; return { f with prefer := some p }
  | "--ff-latency" :: l :: rest => do let f ← hwSelectFlags rest; return { f with lat := some l }
  | "--budget" :: b :: rest => do let f ← hwSelectFlags rest; return { f with budget := some b }
  | "--out" :: o :: rest => do let f ← hwSelectFlags rest; return { f with out := some o }
  | "--table" :: rest => do let f ← hwSelectFlags rest; return { f with table := true }
  | _ => none

/-- `--artifact d`, `--target t`, `--out o` of `cqr hw check`, in any position. -/
def hwCheckFlags : List String → Option (Option String × Option String × Option String)
  | [] => some (none, none, none)
  | "--artifact" :: d :: rest => do
    let (_, t, o) ← hwCheckFlags rest
    return (some d, t, o)
  | "--target" :: t :: rest => do
    let (d, _, o) ← hwCheckFlags rest
    return (d, some t, o)
  | "--out" :: o :: rest => do
    let (d, t, _) ← hwCheckFlags rest
    return (d, t, some o)
  | _ => none

/-- `--target t` and `--json` of `cqr hw bound`, in any position; the other flags are left. -/
def hwBoundFlags : List String → Option (Option String × Bool × List String)
  | [] => some (none, false, [])
  | "--target" :: t :: rest => do
    let (_, j, r) ← hwBoundFlags rest
    return (some t, j, r)
  | "--json" :: rest => do
    let (t, _, r) ← hwBoundFlags rest
    return (t, true, r)
  | f :: rest => do
    let (t, j, r) ← hwBoundFlags rest
    return (t, j, f :: r)

/-- PHASE2_SPEC §C.1 "Per-operation rates" (Stage 24c) — `cqr hw bound <file.cqr> --target
<target.json> [--solutions M] [--iterations r] [--shape tree|few:log] [--uncompute mbu|coherent]
[--json]`: the Grover circuit by the same `groverInstance` as `cqr certify`, δ by `groverDelta`,
the counts under the table of the target's basis (`basisCounts`), the rates (worst and median over
the device) from the snapshot, each product, the sum, the worst-case δ_hw (vacuous at ≥ 1), the
median figure (typical, not a bound) and the coefficient of η_mid (the mid-circuit measurements,
which take the readout rate as a labelled assumption); the final readout of the `n` data qubits is
added. `mbu` on a target without feed-forward: exit 2. Nothing is written; the output says
"reported, not certified (Stage 27)". -/
def runHwBound (path target : String) (solutions iters : Option Nat) (dif : CertDiffusion)
    (mode : UncomputeMode) (json : Bool) : IO UInt32 := do
  let t ← match ← Hardware.readTarget target with
    | .error msg => IO.eprintln s!"cqr hw bound: {msg}"; return 2
    | .ok t => pure t
  let basis ← match Hardware.TargetBasis.ofGates t.basisGates with
    | .error msg => IO.eprintln s!"cqr hw bound: {target}: {msg}"; return 2
    | .ok b => pure b
  if mode == .mbu && !t.capabilities.feedForward.value then
    IO.eprintln s!"cqr hw bound: mbu needs feed-forward; the target {t.name} supports coherent only"
    return 2
  let rates ← match Hardware.Rates.ofTarget t basis with
    | .error msg => IO.eprintln s!"cqr hw bound: {target}: {msg}"; return 2
    | .ok r => pure r
  match ← frontEnd path, ← signature path solutions with
  | .error d, _ | _, .error d => IO.println d.toJson.compress; return 1
  | .ok (tp, _), .ok sig =>
    let gi ← match groverInstance tp sig iters dif mode with
      | .ok gi => pure gi
      | .error (.diagnostic d) => IO.println d.toJson.compress; return 1
      | .error (.usage msg) => IO.eprintln s!"cqr hw bound: {msg}"; return 2
    let some M := gi.M
      | IO.eprintln "cqr hw bound: the bound needs the solution count M (from ℰ or --solutions M)"
        return 2
    let delta := groverDelta gi.r gi.n M
    let R := Hardware.BoundReport.mk' basis gi.circuit gi.n rates delta
    let c := R.counts
    let two := basis.twoQubit
    let shape : String := match dif with | .tree => "tree" | .fewLog => "few:log"
    let modeS : String := match mode with | .mbu => "mbu" | .coherent => "coherent"
    let rs := Hardware.ratStr
    let term (n : Nat) (r : Hardware.Rate) : Rat := n * r.worst
    let termM (n : Nat) (r : Hardware.Rate) : Rat := n * r.median
    let meas := c.midMeas + c.finalMeas + R.readoutData
    let sumW := term c.rz rates.rz + term c.sx rates.sx + term c.x rates.x +
      term c.twoQubit rates.twoQubit + term meas rates.readout
    let sumM := termM c.rz rates.rz + termM c.sx rates.sx + termM c.x rates.x +
      termM c.twoQubit rates.twoQubit + termM meas rates.readout
    if json then
      let rate (r : Hardware.Rate) : Lean.Json := Lean.Json.mkObj
        [("worst", rs r.worst), ("median", rs r.median), ("entries", r.entries)]
      IO.println (Lean.Json.mkObj
        [("target", t.name), ("basis", two), ("source", path), ("shape", shape),
         ("uncompute", modeS), ("n", gi.n), ("r", gi.r), ("M", M),
         ("counts", Lean.Json.mkObj [("rz", c.rz), ("sx", c.sx), ("x", c.x), (two, c.twoQubit),
           ("mid_circuit_measurements", c.midMeas), ("final_measurements", c.finalMeas),
           ("data_readout", R.readoutData), ("measurements_total", meas), ("total", c.total + R.readoutData)]),
         ("rates", Lean.Json.mkObj [("rz", rate rates.rz), ("sx", rate rates.sx), ("x", rate rates.x),
           (two, rate rates.twoQubit), ("readout", rate rates.readout)]),
         ("terms_worst", Lean.Json.mkObj [("rz", rs (term c.rz rates.rz)), ("sx", rs (term c.sx rates.sx)),
           ("x", rs (term c.x rates.x)), (two, rs (term c.twoQubit rates.twoQubit)),
           ("measurements", rs (term meas rates.readout)), ("sum", rs sumW)]),
         ("terms_median", Lean.Json.mkObj [("rz", rs (termM c.rz rates.rz)), ("sx", rs (termM c.sx rates.sx)),
           ("x", rs (termM c.x rates.x)), (two, rs (termM c.twoQubit rates.twoQubit)),
           ("measurements", rs (termM meas rates.readout)), ("sum", rs sumM)]),
         ("delta", rs delta),
         ("bound", Lean.Json.mkObj [("worst", rs R.worst), ("worst_vacuous", R.vacuous),
           ("median", rs R.median), ("median_float", Lean.toJson (Hardware.ratFloat R.median)),
           ("median_label", "typical, not a bound")]),
         ("eta_mid_coefficient", R.etaMidCoeff),
         ("mid_circuit_assumption", "mid-circuit measurements take the readout rate (the snapshot gives no mid-circuit error)"),
         ("status", "reported, not certified (Stage 27)")]).compress
      return 0
    IO.println s!"target: {t.name} (basis {two}); {path}: shape {shape}, uncompute {modeS}, n = {gi.n}, r = {gi.r}, M = {M}"
    IO.println s!"counts under the table: rz {c.rz}, sx {c.sx}, x {c.x}, {two} {c.twoQubit}, mid-circuit measurements {c.midMeas}, final measurements {c.finalMeas}, data readout {R.readoutData} (measurements {meas}; total {c.total + R.readoutData})"
    let line (name : String) (n : Nat) (r : Hardware.Rate) : IO Unit :=
      IO.println s!"  {name}: {n} × worst {rs r.worst} = {rs (term n r)}  |  median {rs r.median} ({r.entries} entries)"
    IO.println "rates over the device (worst | median) and the worst-case terms:"
    line "rz" c.rz rates.rz
    line "sx" c.sx rates.sx
    line "x" c.x rates.x
    line two c.twoQubit rates.twoQubit
    line "measurements (readout rate; mid-circuit by assumption)" meas rates.readout
    IO.println s!"  sum (worst) = {rs sumW}; sum (median) = {rs sumM}"
    IO.println s!"δ = {rs delta}"
    IO.println s!"δ_hw ≤ δ + Σ count · rate = {rs R.worst} (worst case over the device, a bound for any layout){if R.vacuous then " — VACUOUS (≥ 1)" else ""}"
    IO.println s!"median figure: {rs R.median} ≈ {Hardware.ratFloat R.median} (typical, not a bound)"
    IO.println s!"coefficient of η_mid (mid-circuit measurements, readout rate assumed): {R.etaMidCoeff}"
    IO.println "reported, not certified (Stage 27)"
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", file] => runCheck file
  | ["check", file, "--truth-table"] => runTruthTable file
  | ["extract", file] => runExtract file none
  | ["extract", file, "--solutions", m] =>
    match m.toNat? with
    | some m => runExtract file (some m)
    | none => IO.eprintln s!"cqr extract: --solutions expects a natural number, got `{m}`"; return 2
  | "extract" :: file :: flags =>
    -- Stage 21a1: `--problem search|count` and `--precision m`, in any order with `--solutions`
    match requestFlags false flags with
    | some f =>
      match problemOf f with
      | some p => runExtract file f.solutions p
      | none => IO.eprint usage; return 2
    | none => IO.eprint usage; return 2
  | "match" :: file :: flags =>
    match matchFlags flags with
    | some (m, t) => runMatch file m t
    | none =>
      -- Stage 21a1: the request flags `--problem` / `--precision` (any order; usage errors exit 2)
      match requestFlags true flags with
      | some f =>
        match problemOf f with
        | some p => runMatch file f.solutions f.text p
        | none => IO.eprint usage; return 2
      | none => IO.eprint usage; return 2
  | "synthesize" :: "--diffusion" :: n :: flags =>
    match n.toNat?, shapeFlag flags with
    | some n, some (sh, flags) =>
      match uncomputeFlag flags with
      | some (mode, flags) =>
        match synthFlags flags with
        | some (k, j, l) => runDiffusion n k sh mode j l
        | none => IO.eprint usage; return 2
      | none => IO.eprint usage; return 2
    | _, _ => IO.eprint usage; return 2
  | "synthesize" :: file :: "--grover" :: flags =>
    match shapeFlag flags with
    | some (sh, flags) =>
      match uncomputeFlag flags with
      | some (mode, flags) =>
        match groverFlags flags with
        | some (r, m, j, l) => runGrover file r m sh mode j l
        | none => IO.eprint usage; return 2
      | none => IO.eprint usage; return 2
    | none => IO.eprint usage; return 2
  | "synthesize" :: file :: flags =>
    match uncomputeFlag flags with
    | some (mode, flags) =>
      match synthFlags flags with
      | some (k, j, l) => runSynthesize file k mode j l
      | none => IO.eprint usage; return 2
    | none => IO.eprint usage; return 2
  | "certify" :: file :: flags =>
    -- Stage 21a4 (PHASE2_SPEC.md §A.6 (8)): `--budget` / `--prefer` (both or neither); a flag
    -- list without them is parsed exactly as before
    match selectionFlags flags with
    | none => IO.eprint usage; return 2
    | some (some bStr, some pStr, flags) =>
      match parseBudget bStr, Pref.parse? pStr with
      | some budget, some pref =>
        if flags.contains "--shape" || flags.contains "--uncompute" || flags.contains "--problem" ||
            flags.contains "--precision" then
          IO.eprint usage; return 2
        match certifyFlags flags with
        | some (m, r, o, b, p, h, c) =>
          runCertifySelect file budget pref m r o b p h (c.getD defaultCountLimit)
        | none => IO.eprint usage; return 2
      | _, _ => IO.eprint usage; return 2
    | some (some _, none, _) | some (none, some _, _) => IO.eprint usage; return 2
    | some (none, none, flags) =>
    -- Stage 21a3 (PHASE2_SPEC.md §A.5 (5)): the request flags `--problem` / `--precision`; a flag
    -- list without them is parsed exactly as before
    match certifyRequest flags with
    | none => IO.eprint usage; return 2
    | some (some "count", some m, flags) =>
      match shapeFlag flags with
      | some (.std .tree, flags) =>
        match uncomputeFlag flags with
        | some (mode, flags) =>
          match certifyFlags flags with
          | some (none, none, o, b, p, none, c) =>
            runCertifyCount file m o b p (c.getD defaultCountLimit) mode
          | some _ =>
            IO.eprintln "cqr certify: --problem count does not take --solutions, --iterations or \
              --profile (PHASE2_SPEC §A.5 amendment (5))"
            return 2
          | none => IO.eprint usage; return 2
        | none => IO.eprint usage; return 2
      | some (sh, _) =>
        IO.eprintln s!"cqr certify: --problem count takes --shape tree only, not --shape \
          {shapeName sh} (PHASE2_SPEC §A.5 amendment (5))"
        return 2
      | none => IO.eprint usage; return 2
    | some (some "count", none, _) => IO.eprint usage; return 2
    | some (_, some _, _) => IO.eprint usage; return 2
    | some (_, none, flags) =>
      match shapeFlag flags with
      | some (sh, flags) =>
        match uncomputeFlag flags with
        | some (mode, flags) =>
          match certDiffusionOf sh, certifyFlags flags with
          | some dif, some (m, r, o, b, p, h, c) =>
            if dif == .fewLog && mode == .coherent then
              IO.println (Diagnostic.at .synthesis .unsupportedCombination ⟨1, 1⟩
                "the few-ancilla MCZ is MBU-only (Stage 15): --shape few:log does not take \
                --uncompute coherent").toJson.compress
              return 1
            runCertify file m r o b p h dif (c.getD defaultCountLimit) mode
          | none, _ =>
            IO.eprintln s!"cqr certify: --shape {shapeName sh} has no certificate path \
              (certified: tree, few:log)"
            return 2
          | _, none => IO.eprint usage; return 2
        | none => IO.eprint usage; return 2
      | none => IO.eprint usage; return 2
  | "emit" :: file :: flags =>
    match emitFlags flags with
    | some (some f, r, m, o) => runEmit file f r m o
    | _ => IO.eprint usage; return 2
  | ["hw", "capabilities", target] => runHwCapabilities target
  | ["hw", "table", "--basis", b] =>
    -- Stage 26a (PHASE2_SPEC §C.3): the Lean decomposition table as JSON, in hw/decomp.py's format
    match b with
    | "cz" => IO.println (Hardware.tableJson .cz).compress; return 0
    | "cx" => IO.println (Hardware.tableJson .cx).compress; return 0
    | _ => IO.eprint usage; return 2
  | "hw" :: "select" :: flags =>
    match hwSelectFlags flags with
    | some f =>
      match f.request, f.target, f.prefer with
      | some r, some t, some p => runHwSelect r t p f.lat f.budget f.out f.table
      | _, _, _ => IO.eprint usage; return 2
    | none => IO.eprint usage; return 2
  | "hw" :: "certify" :: flags =>
    match hwCertifyFlags flags with
    | some (some c, some a, some t, some l, o) => runHwCertify c a t l o
    | _ => IO.eprint usage; return 2
  | "hw" :: "noisecert" :: flags =>
    match hwNoiseCertFlags flags with
    | some (some a, some t, some l, c, o) => runHwNoiseCert a t l c o
    | _ => IO.eprint usage; return 2
  | "hw" :: "noise" :: flags =>
    match hwNoiseFlags flags with
    | some (some d, some t, j) => runHwNoise d t j
    | _ => IO.eprint usage; return 2
  | "hw" :: "grade" :: flags =>
    match hwGradeFlags flags with
    | some (some d, some t, some l, j) => runHwGrade d t l j
    | _ => IO.eprint usage; return 2
  | "hw" :: "check" :: flags =>
    match hwCheckFlags flags with
    | some (some d, some t, o) => runHwCheck d t (o.getD "examples/hw_checks")
    | _ => IO.eprint usage; return 2
  | "hw" :: "bound" :: file :: flags =>
    match hwBoundFlags flags with
    | some (some target, json, flags) =>
      match shapeFlag flags with
      | some (sh, flags) =>
        match uncomputeFlag flags with
        | some (mode, flags) =>
          match certDiffusionOf sh, certifyFlags flags with
          | some dif, some (m, r, none, none, false, none, none) =>
            runHwBound file target m r dif mode json
          | none, _ =>
            IO.eprintln s!"cqr hw bound: --shape {shapeName sh} has no certificate path (tree, few:log)"
            return 2
          | _, _ => IO.eprint usage; return 2
        | none => IO.eprint usage; return 2
      | none => IO.eprint usage; return 2
    | _ => IO.eprint usage; return 2
  | "hw" :: _ => IO.eprint usage; return 2
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
