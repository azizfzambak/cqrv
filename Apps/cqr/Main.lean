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

open CQRV CQRV.DSL CQRV.Matching CQRV.Synthesis CQRV.Certify CQRV.Emit

/-- Subcommands and the stage (docs/PLAN.md) that implements each. -/
def subcommands : List (String × Nat) :=
  [("check", 3), ("extract", 3), ("match", 4), ("synthesize", 5), ("certify", 8), ("emit", 8)]

def usage : String :=
  "usage: cqr <command> [args]\n\ncommands:\n" ++
    "  check <file>\n  extract <file> [--solutions M]\n  match <file> [--solutions M] [--text]\n" ++
    "  synthesize <file> [--amax k] [--uncompute mbu|coherent] [--json] [--layers]\n" ++
    "  synthesize --diffusion n [--shape tree|chain|few:ladder|few:log] [--amax k] [--uncompute mbu|coherent] [--json] [--layers]\n" ++
    "  synthesize <file> --grover [--shape tree|chain|few:ladder|few:log] [--iterations r] [--solutions M] [--uncompute mbu|coherent] [--json] [--layers]\n" ++
    "  check <file> --truth-table\n" ++
    "  certify <file> [--solutions M] [--iterations r] [--out dir] [--bench k] [--report]\n" ++
    "          [--profile name|path] [--shape tree|few:log] [--count-limit k] [--uncompute mbu|coherent]\n" ++
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
    | .error (.diagnostic d) => IO.println d.toJson.compress; return 1
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
    let (subst, sides) ← match matchLibrary library t with
      | .matched _ σ ds =>
        let σs := σ.mergeSort fun a b => Term.MVar.cmp a.1 b.1 != .gt
        pure (", ".intercalate (σs.map fun (m, b) => s!"{m.name} ↦ {b.toJson.compress}"),
          ds.map fun d => s!"{d.cond.render}: {d.render}")
      | r => return (← printNoMatch "certify" t r false)
    let gi ← match groverInstance tp sig iters diff mode with
      | .ok gi => pure gi
      | .error (.diagnostic d) => IO.println d.toJson.compress; return 1
      | .error (.usage msg) => IO.eprintln s!"cqr certify: {msg}"; return 2
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
    let text := renderCert q
    -- the QIR text (Stage 17b: `emitQIR` can refuse a circuit; nothing is written then)
    let qirText ← match emitQIR tp.name gi.circuit with
      | .ok t => pure t
      | .error d => IO.println d.toJson.compress; return 1
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
      proofHash := some (proofHash text cfg.lean cfg.mathlib cfg.physlib), axioms := last.axioms,
      status, theoremName := some q.theoremName, obligations, hardware := hw, diffusion := diff }
    -- compact, keys sorted (canonical, as `circuit_hash` and `CertifyTool sample`)
    IO.FS.writeFile (file "certificate.json") (cert.toJson.compress ++ "\n")
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
          axioms := last.axioms, statusLine, certified := status == .certified,
          hardware := hw, diffusionShape := diff, count, uncompute := mode }
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
    if let some h := hw then IO.println h.statusLine
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
