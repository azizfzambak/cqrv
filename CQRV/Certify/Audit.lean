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

/-- Run a command; its trimmed stdout on exit code 0. -/
def commandOutput (cmd : String) (args : Array String) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd, args }
    if out.exitCode != 0 then return none
    let s := out.stdout.trimAscii.toString
    return if s.isEmpty then none else some s
  catch _ => return none

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
`Win32_Processor` (`MaxClockSpeed`), macOS from `sysctl`; `none` where unavailable. -/
def detectMachine : IO (Option String × Option Nat × Option String) := do
  if ← System.FilePath.pathExists "/proc/cpuinfo" then
    let info ← IO.FS.readFile "/proc/cpuinfo"
    let cpus := ((info.splitOn "\n").filter fun l => l.startsWith "processor").length
    let maxKHz ← try
        some <$> IO.FS.readFile "/sys/devices/system/cpu/cpu0/cpufreq/cpuinfo_max_freq"
      catch _ => pure none
    let clock := maxKHz.bind fun s =>
      s.trimAscii.toString.toNat?.map fun k => s!"{k / 1000} MHz (max)"
    return (cpuinfoField info "model name", if cpus == 0 then none else some cpus, clock)
  if System.Platform.isWindows then
    let q := "$p = Get-CimInstance Win32_Processor | Select-Object -First 1; " ++
      "\"$($p.Name)|$($p.NumberOfLogicalProcessors)|$($p.MaxClockSpeed)\""
    match ← commandOutput "powershell" #["-NoProfile", "-NonInteractive", "-Command", q] with
    | some s =>
      match s.splitOn "|" with
      | [name, cpus, mhz] =>
        return (some name.trimAscii.toString, cpus.trimAscii.toString.toNat?,
          mhz.trimAscii.toString.toNat?.map fun m => s!"{m} MHz (max)")
      | _ => pure ()
    | none => pure ()
    let cpus := (← IO.getEnv "NUMBER_OF_PROCESSORS").bind (·.toNat?)
    return (← IO.getEnv "PROCESSOR_IDENTIFIER", cpus, none)
  let name ← commandOutput "sysctl" #["-n", "machdep.cpu.brand_string"]
  let cpus ← commandOutput "sysctl" #["-n", "hw.logicalcpu"]
  return (name, cpus.bind (·.toNat?), none)

end CQRV.Certify

end
