module

public import CQRV.Certify.Generate

/-!
# CQRV.Certify.Audit

Report §9.5.1 (master discipline: "certified" only when the proof term is sorry-free and
axiom-audited), §9.5.3 (CI kernel-checks certificates; the audit is blocking), §5.1.3 (the
per-request work is a kernel check) — Stage 8b task 2, reviewer decisions 2 and 3
(DECISIONS.md 2026-10-25).

* `kernelCheck path`: runs `lake env lean -Dprofiler=true <path>` (the file ends with
  `#print axioms cert`) and records the exit code, the output, the wall time and the kernel time
  (`type checking` of the profiler's cumulative times).
* `parseAxioms thm out`: the axiom list of `#print axioms thm` in Lean's output.
* `auditAxioms axs`: passes iff `sorryAx ∉ axs` and every axiom is one of `propext`,
  `Classical.choice`, `Quot.sound` or listed in `trustBoundary` (empty today).

The CLI only writes text and runs Lean; whether a certificate is certified is decided by the
kernel's exit code and the axioms the kernel-checked environment reports.
-/

@[expose] public section

namespace CQRV.Certify

/-! ## R5 — the library hash of the working tree -/

/-- R5 (REVIEW_RESPONSE_1 §4) — the files of `libraryHash`: every `.lean` file under `CQRV/` and
`Apps/` (recursively) and `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, read as bytes
from the working directory (the project root, where `cqr` runs); paths with `/`. -/
def libraryFiles : IO (List (String × ByteArray)) := do
  let mut out : List (String × ByteArray) := []
  for root in ["CQRV", "Apps"] do
    for p in ← System.FilePath.walkDir ⟨root⟩ do
      if p.extension == some "lean" then
        out := (p.toString.replace "\\" "/", ← IO.FS.readBinFile p) :: out
  for f in ["lakefile.lean", "lean-toolchain", "lake-manifest.json"] do
    out := (f, ← IO.FS.readBinFile ⟨f⟩) :: out
  return out

/-- R5 — `hashes.library` of the working tree (`libraryHash` over `libraryFiles`). -/
def libraryHashIO : IO String := do return libraryHash (← libraryFiles)

/-! ## The axiom audit (decision 3) -/

/-- Report §9.5.1 — the standard axioms of Lean/Mathlib accepted by every certificate. -/
def standardAxioms : List String := ["propext", "Classical.choice", "Quot.sound"]

/-- Report §9.5.1 — the named trust-boundary table: further axioms a certificate may depend on,
each with its justification (a DECISIONS.md entry). Empty today; `sorryAx` can never be added
(`auditAxioms` rejects it first). -/
def trustBoundary : List (String × String) := []

/-- Result of the axiom audit: pass, or the offending axioms. -/
inductive AuditResult where
  | pass
  | fail (offending : List String)
  deriving Repr, DecidableEq

/-- Report §9.5.1, decision 3 — the audit passes iff the list contains no `sorryAx` and every
axiom is standard or in `trustBoundary`. -/
def auditAxioms (axs : List String) : AuditResult :=
  let ok (a : String) := a != "sorryAx" &&
    (standardAxioms.contains a || (trustBoundary.map (·.1)).contains a)
  match axs.filter (!ok ·) with
  | [] => .pass
  | bad => .fail bad

/-- `"[propext, Classical.choice]"` (after the colon of `#print axioms`) as a list. -/
def parseAxiomList (s : String) : Option (List String) := do
  let s := s.trimAscii.toString
  guard (s.startsWith "[" && s.endsWith "]")
  let inner := ((s.drop 1).dropEnd 1).toString
  if inner.trimAscii.isEmpty then return []
  return (inner.splitOn ",").map (·.trimAscii.toString)

/-- Report §9.5.3, decision 2 — the axioms of `thm` as printed by `#print axioms thm` in Lean's
output (`'thm' depends on axioms: [...]`, the list possibly wrapped over several lines, or
`'thm' does not depend on any axioms`); `none` when the message is missing or occurs more than
once. -/
def parseAxioms (thm out : String) : Option (List String) :=
  let dep := s!"'{thm}' depends on axioms: "
  let none' := s!"'{thm}' does not depend on any axioms"
  match out.splitOn dep, (out.splitOn none').length with
  | [_, rest], 1 =>
    match rest.splitOn "]" with
    | list :: _ :: _ => parseAxiomList ((list.replace "\r" "").replace "\n" " " ++ "]")
    | _ => none
  | [_], 2 => some []
  | _, _ => none

/-! ## The kernel check (decision 2) -/

/-- Seconds in a profiler time, `7.65s` / `163ms` / `12μs`, as milliseconds. -/
def parseProfilerMs (s : String) : Option Nat := do
  let s := s.trimAscii.toString
  let (num, scale) ←
    if s.endsWith "ms" then some ((s.dropEnd 2).toString, 1)
    else if s.endsWith "μs" then some ((s.dropEnd 2).toString, 0)
    else if s.endsWith "s" then some ((s.dropEnd 1).toString, 1000)
    else none
  let (ip, fp) := match num.splitOn "." with
    | [i, f] => (i, f)
    | _ => (num, "")
  let i ← ip.toNat?
  let f ← if fp.isEmpty then some 0 else fp.toNat?
  -- value = i + f / 10^|fp|, in units of `scale` ms
  return (i * 10 ^ fp.length + f) * scale / 10 ^ fp.length

/-- The kernel time: `type checking <t>` in the profiler's cumulative times. -/
def parseKernelMs (out : String) : Option Nat :=
  let hits := (out.splitOn "\n").filterMap fun l =>
    let l := (l.dropEndWhile (· == '\r')).toString
    match l.splitOn "\ttype checking " with
    | ["", t] => parseProfilerMs t
    | _ => none
  hits.getLast?

/-- Result of `lake env lean` on a certificate file. -/
structure KernelCheck where
  exitCode : UInt32
  output : String
  wallMs : Nat
  kernelMs : Option Nat

/-- Report §5.1.3, §9.5.3 — kernel-check a certificate file: `lake env lean -Dprofiler=true
<path>` in the current directory (the project root), stdout and stderr together. -/
def kernelCheck (path : String) : IO KernelCheck := do
  let t0 ← IO.monoMsNow
  let out ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", "-Dprofiler=true", path] }
  let t1 ← IO.monoMsNow
  let output := out.stdout ++ out.stderr
  return { exitCode := out.exitCode, output, wallMs := t1 - t0,
           kernelMs := parseKernelMs output }

/-- The outcome of kernel check + audit for one certificate file. -/
structure AuditOutcome where
  check : KernelCheck
  axioms : List String
  result : AuditResult

/-- Report §9.5.1, §9.5.3 — kernel-check `path` and audit the axioms of `thm`: `.error` when
Lean fails or the `#print axioms` line is missing (no certificate at all). -/
def checkAndAudit (path thm : String) : IO (Except String AuditOutcome) := do
  let kc ← kernelCheck path
  if kc.exitCode != 0 then
    return .error s!"kernel check failed (lake env lean exit {kc.exitCode}):\n{kc.output}"
  let some axs := parseAxioms thm kc.output
    | return .error s!"no `#print axioms {thm}` line in the Lean output:\n{kc.output}"
  return .ok { check := kc, axioms := axs, result := auditAxioms axs }

/-! ## The machine (decision 6, §9.5.1 reference configuration) -/

/-- The outcome of `runCommand` (Stage 18b B0): the trimmed stdout, `failed` (non-zero exit,
empty output or a command that could not be spawned), or `timedOut`. -/
inductive CommandResult where
  | ok (s : String)
  | failed
  | timedOut
  deriving Repr, DecidableEq, Inhabited

/-- Stage 18b B0 (docs/tasks/STAGE18_TASK.md) — run a command with a wall-clock timeout: the
child is spawned with piped output (`IO.Process.spawn`), read by a background task, and polled
with `IO.Process.Child.tryWait` every 20 ms until it exits or `timeoutMs` have passed; on timeout
it is killed (`IO.Process.Child.kill`) and reaped, and the result is `.timedOut`. The machine
detection of `detectMachine` must never block a certificate (the first CI run of Stage 18a
waited 2.5 h on a `powershell` that did not start). -/
def runCommand (cmd : String) (args : Array String) (timeoutMs : Nat) : IO CommandResult := do
  try
    let child ← IO.Process.spawn
      { cmd, args, stdin := .null, stdout := .piped, stderr := .piped }
    let outTask ← IO.asTask child.stdout.readToEnd
    let errTask ← IO.asTask child.stderr.readToEnd
    let t0 ← IO.monoMsNow
    let mut code : Option UInt32 := none
    repeat
      match ← child.tryWait with
      | some c => code := some c; break
      | none =>
        if (← IO.monoMsNow) - t0 ≥ timeoutMs then break
        IO.sleep 20
    match code with
    | none =>
      child.kill
      let _ ← child.wait
      return .timedOut
    | some c =>
      let out ← IO.ofExcept (← IO.wait outTask)
      let _ ← IO.wait errTask
      if c != 0 then return .failed
      let s := out.trimAscii.toString
      return if s.isEmpty then .failed else .ok s
  catch _ => return .failed

/-- Run a command; its trimmed stdout on exit code 0 within `timeoutMs` (`runCommand`). -/
def commandOutput (cmd : String) (args : Array String) (timeoutMs : Nat) : IO (Option String) := do
  match ← runCommand cmd args timeoutMs with
  | .ok s => return some s
  | _ => return none

/-- The timeout of every machine-detection command (Stage 18b B0): 20 s. -/
def machineCommandTimeoutMs : Nat := 20000

/-- What `detectMachine` found: CPU model, number of logical CPUs, clock, and the
machine-detection commands that hit `machineCommandTimeoutMs` (`cqr certify` names them on
stderr; the fields then come from the environment). -/
structure MachineInfo where
  cpu : Option String
  logicalCpus : Option Nat
  clock : Option String
  timedOut : List String := []
  deriving Repr, Inhabited

/-- The value of the first `key : value` line of `/proc/cpuinfo`. -/
def cpuinfoField (info key : String) : Option String :=
  (info.splitOn "\n").findSome? fun l =>
    match l.splitOn ":" with
    | k :: v :: rest =>
      if k.trimAscii.toString == key then some (":".intercalate (v :: rest)).trimAscii.toString
      else none
    | _ => none

/-- Report §9.5.1 — CPU model, number of logical CPUs and clock of this machine: Linux from
`/proc/cpuinfo` (clock: `cpuinfo_max_freq`, not the fluctuating current `cpu MHz`), Windows from
`Win32_Processor` (`MaxClockSpeed`), macOS from `sysctl`; `none` where unavailable. Every
command runs under `machineCommandTimeoutMs` (Stage 18b B0); a command that times out is
listed in `timedOut` and the Windows fields fall back to `PROCESSOR_IDENTIFIER` /
`NUMBER_OF_PROCESSORS` (no clock). -/
def detectMachine : IO MachineInfo := do
  if ← System.FilePath.pathExists "/proc/cpuinfo" then
    let info ← IO.FS.readFile "/proc/cpuinfo"
    let cpus := ((info.splitOn "\n").filter fun l => l.startsWith "processor").length
    let maxKHz ← try
        some <$> IO.FS.readFile "/sys/devices/system/cpu/cpu0/cpufreq/cpuinfo_max_freq"
      catch _ => pure none
    let clock := maxKHz.bind fun s =>
      s.trimAscii.toString.toNat?.map fun k => s!"{k / 1000} MHz (max)"
    return { cpu := cpuinfoField info "model name",
             logicalCpus := if cpus == 0 then none else some cpus, clock }
  if System.Platform.isWindows then
    let q := "$p = Get-CimInstance Win32_Processor | Select-Object -First 1; " ++
      "\"$($p.Name)|$($p.NumberOfLogicalProcessors)|$($p.MaxClockSpeed)\""
    let timedOut ← match ← runCommand "powershell"
        #["-NoProfile", "-NonInteractive", "-Command", q] machineCommandTimeoutMs with
      | .ok s =>
        match s.splitOn "|" with
        | [name, cpus, mhz] =>
          return { cpu := some name.trimAscii.toString, logicalCpus := cpus.trimAscii.toString.toNat?,
                   clock := mhz.trimAscii.toString.toNat?.map fun m => s!"{m} MHz (max)" }
        | _ => pure []
      | .failed => pure []
      | .timedOut => pure ["powershell -NoProfile -NonInteractive -Command (Get-CimInstance Win32_Processor)"]
    let cpus := (← IO.getEnv "NUMBER_OF_PROCESSORS").bind (·.toNat?)
    return { cpu := ← IO.getEnv "PROCESSOR_IDENTIFIER", logicalCpus := cpus, clock := none, timedOut }
  let mut timedOut : List String := []
  let name ← match ← runCommand "sysctl" #["-n", "machdep.cpu.brand_string"]
      machineCommandTimeoutMs with
    | .ok s => pure (some s)
    | .failed => pure none
    | .timedOut => timedOut := timedOut ++ ["sysctl -n machdep.cpu.brand_string"]; pure none
  let cpus ← match ← runCommand "sysctl" #["-n", "hw.logicalcpu"] machineCommandTimeoutMs with
    | .ok s => pure s.toNat?
    | .failed => pure none
    | .timedOut => timedOut := timedOut ++ ["sysctl -n hw.logicalcpu"]; pure none
  return { cpu := name, logicalCpus := cpus, clock := none, timedOut }

end CQRV.Certify

end
