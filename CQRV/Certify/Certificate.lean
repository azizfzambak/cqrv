module

public import Lean.Data.Json
public import CQRV.Certify.SHA3
public import CQRV.Certify.FrontEnd
public import CQRV.DSL.Basic
public import CQRV.Matching.Basic
public import CQRV.Synthesis.Basic
public import CQRV.Grades.Profile

/-!
# CQRV.Certify.Certificate

Report §8.4.2 (certificate structure), §8.4.4 (certificate contents), §9.5.1 (reference
configuration), §9.5.3 (JSON envelope), §3.3.3 (`δ_hw = δ + G·p̄`) — the certificate record and
its JSON form, schema v1.0.0 (`docs/certificate.schema.json`; DECISIONS.md 2026-10-24, Stage 8a
reviewer decisions 2 and 3).

* `groverSuccess r s`: the exact success probability `sin²((2r+1)θ)` with `s = sin²θ = M/2ⁿ`,
  from `sin((2r+1)θ) = sin θ · U_{2r}(cos θ)` (Chebyshev polynomials of the second kind),
  computed in `ℚ[c]/(c² − (1 − s))`: `U_{2r}` is even, so its value is rational.
* Hashes (decision 2): `predicateHash` (DSL source with line endings normalized to LF),
  `circuitHash` (`Circuit.toJson`, compact; `Json` objects keep their keys sorted),
  `proofHash` (the certificate `.lean` file of Stage 8b with the pinned configuration).
* `Certificate.build`: the record from the pipeline's data, with `proof`, `cpu`, `axioms`
  empty and `status = notYetAudited`; `cqr certify` (Stage 8b) fills them after the kernel check
  and the axiom audit (`CQRV.Certify.Audit`). Schema v1.1.0 (Stage 8b) adds `theorem`,
  `obligations` and the machine fields of `reference_configuration`; v1.2.0 (Stage 8b review)
  adds `trust_boundary.front_end` (`frontEndTrust`); v1.3.0 (Stage 9b, decision 1) lets it be
  the exhaustive-validation wording (`frontEndValidatedText n`, `CQRV.Certify.FrontEnd`);
  v1.4.0 (Stage 11b, decision 5) adds the optional object `hardware` (`cqr certify --profile`).
  A certificate without `hardware` is written exactly as before, `schema_version` "1.3.0"
  included (it is valid under both); one with `hardware` says "1.4.0". v1.5.0 (Stage 12d,
  decision 5) adds the optional field `diffusion_shape` (`"tree"` when omitted): only a
  certificate of `cqr certify --shape few:log` carries it (`"few:log"`) and says "1.5.0", so
  the tree certificates stay byte-identical. v1.6.0 (Stage 14a, DECISIONS.md 2026-10-29) adds
  the required object `solution_count` `{value, status}` (`CountStatus`: `kernel_decided` when
  `Cert.lean` proves `hM_count` by `Network.countSat_eq_card` and `decide +kernel`, `hypothesis`
  when `cert` keeps `hM_card`); every certificate now says "1.6.0", and `hardware` /
  `diffusion_shape` are optional under it.
-/

@[expose] public section

namespace CQRV.Certify

open Lean CQRV.DSL CQRV.Matching CQRV.Synthesis

/-! ## Exact success probability -/

/-- `a + b·c` in `ℚ[c]/(c² − (1 − s))`, as the pair `(a, b)`; multiplication by `2c`. -/
def twoCTimes (s : Rat) (p : Rat × Rat) : Rat × Rat := (2 * p.2 * (1 - s), 2 * p.1)

/-- Chebyshev `U_k(c)` in `ℚ[c]/(c² − (1 − s))`: `U₀ = 1`, `U₁ = 2c`,
`U_{k+1} = 2c·U_k − U_{k−1}`. -/
def chebyshevU (s : Rat) : Nat → Rat × Rat
  | k => (go k).1
where
  /-- `(U_k, U_{k+1})` -/
  go : Nat → (Rat × Rat) × (Rat × Rat)
    | 0 => ((1, 0), (0, 2))
    | k + 1 =>
      let (u, v) := go k
      let w := twoCTimes s v
      (v, (w.1 - u.1, w.2 - u.2))

/-- Report §8.2, §8.3.4 — the exact Grover success probability `sin²((2r+1)θ)` for
`s = sin²θ`: `sin²θ · U_{2r}(cos θ)²`; `U_{2r}` has no `c` part (DECISIONS.md 2026-10-24,
"r⋆ in `Float` only chooses r; the certified δ is exact"). -/
def groverSuccess (r : Nat) (s : Rat) : Rat :=
  let u := (chebyshevU s (2 * r)).1
  s * u * u

/-- `s = M / 2ⁿ`. -/
def solutionFraction (n M : Nat) : Rat := (M : Rat) / ((2 ^ n : Nat) : Rat)

/-- Report §8.2 — the exact failure probability `δ = 1 − sin²((2r+1)θ)`, `sin²θ = M/2ⁿ`. -/
def groverDelta (r n M : Nat) : Rat := 1 - groverSuccess r (solutionFraction n M)

/-! ## Hashes (decision 2) -/

/-- Line endings normalized to LF (`\r\n` and a lone `\r` become `\n`). -/
def normalizeLF (s : String) : String := (s.replace "\r\n" "\n").replace "\r" "\n"

/-- Report §9.5.3 — `predicate_hash`: SHA3-256 of the DSL source text, line endings LF. -/
def predicateHash (src : String) : String := SHA3.sha3String (normalizeLF src)

/-- Report §9.5.3 — `circuit_hash`: SHA3-256 of the canonical IR JSON (`Circuit.toJson`,
compressed; object keys are sorted because `Json` objects are ordered maps). -/
def circuitHash (C : Circuit) : String := SHA3.sha3String C.toJson.compress

/-- The separator of the `proof_hash` preimage: one NUL byte (it does not occur in the text
parts). -/
def proofHashSeparator : ByteArray := ByteArray.mk #[0]

/-- Report §9.5.3 — `proof_hash` (computed in Stage 8b): SHA3-256 of
`certificate ‖ 0x00 ‖ "lean-toolchain=" toolchain ‖ 0x00 ‖ "mathlib=" rev ‖ 0x00 ‖
"physlib=" rev`, every part UTF-8, the certificate `.lean` text with LF line endings and the
toolchain line trimmed. -/
def proofHash (certText toolchain mathlibRev physlibRev : String) : String :=
  let parts := [normalizeLF certText, "lean-toolchain=" ++ toolchain.trimAscii.toString,
    "mathlib=" ++ mathlibRev, "physlib=" ++ physlibRev]
  let bytes := match parts.map String.toUTF8 with
    | [] => ByteArray.empty
    | b :: bs => bs.foldl (fun acc x => acc ++ proofHashSeparator ++ x) b
  SHA3.sha3_256Hex bytes

/-! ## The record (decision 3) -/

/-- Report §9.5.1 — certificate status. Stage 8a only produces `notYetAudited`; Stage 8b decides
between the other two after the kernel check and the axiom audit. -/
inductive Status where
  | notYetAudited
  | certified
  | withObligations
  deriving Repr, DecidableEq, Inhabited

/-- JSON value of a status (`docs/certificate.schema.json`, enum of `status`). -/
def Status.name : Status → String
  | .notYetAudited => "not yet audited"
  | .certified => "certified"
  | .withObligations => "certificate with tracked obligations"

/-- Report §9.5.1 — the measured time of the kernel check of a certificate file (Stage 8b,
decision 6): wall time of `lake env lean` (process start, imports, elaboration, kernel) and the
kernel's own time (`type checking` of the Lean profiler), over `runs` runs. -/
structure KernelTiming where
  wallMs : Nat
  kernelMs : Option Nat
  runs : Nat
  statistic : String
  deriving Repr, Inhabited

/-- Report §9.5.1 — the reference configuration: toolchain, dependency revisions, and (Stage 8b)
the machine — CPU model, logical CPUs, clock, `LEAN_NUM_THREADS` — and the measured kernel-check
time. -/
structure RefConfig where
  lean : String
  mathlib : String
  physlib : String
  cpu : Option String := none
  logicalCpus : Option Nat := none
  clock : Option String := none
  leanThreads : Option String := none
  kernelCheck : Option KernelTiming := none
  deriving Repr, Inhabited

/-- The reference configuration from the text of `lean-toolchain` and `lake-manifest.json`
(packages `mathlib` and `Physlib`). -/
def RefConfig.ofFiles (toolchain manifest : String) : Except String RefConfig := do
  let j ← Json.parse manifest
  let pkgs ← (j.getObjValAs? (Array Json) "packages")
  let rev (name : String) : Except String String := do
    let some p := pkgs.find? fun p => (p.getObjValAs? String "name").toOption == some name
      | throw s!"lake-manifest.json: no package `{name}`"
    p.getObjValAs? String "rev"
  return { lean := toolchain.trimAscii.toString, mathlib := ← rev "mathlib",
           physlib := ← rev "Physlib" }

/-- Report §3.3.3 — the noisy operations of the emitted program, counted separately: unitary
gates, mid-circuit measurements, classically controlled gates (the IR), and the terminal
measurements the emitters add (one per data qubit). `alloc` / `free` are bookkeeping and not
counted (DECISIONS.md 2026-10-25, Stage 8a review). -/
structure GateCounts where
  unitary : Nat
  midCircuitMeasurements : Nat
  classicallyControlled : Nat
  terminalMeasurements : Nat
  deriving Repr, DecidableEq

/-- Report §3.3.3 — `G`: every noisy operation (conservative bound `δ_hw ≤ δ + G·p̄`). -/
def GateCounts.total (g : GateCounts) : Nat :=
  g.unitary + g.midCircuitMeasurements + g.classicallyControlled + g.terminalMeasurements

/-- Report §3.3.3 — the operation counts of a circuit, with the terminal measurement of its
data register. -/
def gateCounts (C : Circuit) : GateCounts :=
  let count (p : Gate → Bool) := (C.gates.filter p).length
  { unitary := count fun | .measure _ _ | .ifBit _ _ | .alloc _ | .free _ => false | _ => true
    midCircuitMeasurements := count fun | .measure _ _ => true | _ => false
    classicallyControlled := count fun | .ifBit _ _ => true | _ => false
    terminalMeasurements := C.nData }

/-- Report §8.2, §8.4.1 (Stage 12d decision 3) — the diffusion of a certified Grover circuit: the
V1 balanced-tree diffusion (the default, `groverCircuit`) or the few-ancilla diffusion with
candidate B (`groverCircuitFew … .logDepth`, `cqr certify --shape few:log`). -/
inductive CertDiffusion where
  | tree
  | fewLog
  deriving Repr, DecidableEq, Inhabited

/-- The `--shape` / `diffusion_shape` name of a certified diffusion. -/
def CertDiffusion.name : CertDiffusion → String
  | .tree => "tree"
  | .fewLog => "few:log"

/-- Report §8.2, §5.1.3 (Stage 14a) — how the solution count `M` of a certificate was obtained:
decided by the kernel (`hM_count` in `Cert.lean`, through `Network.countSat_eq_card`; `cqr
certify --count-limit k`, `n ≤ k`), or supplied as the hypothesis `hM_card` of `cert`
(§5.2.4, the only form before Stage 14a). -/
inductive CountStatus where
  | kernelDecided
  | hypothesis
  deriving Repr, DecidableEq, Inhabited

/-- The word of `solution_count.status` (`docs/certificate.schema.json`). -/
def CountStatus.name : CountStatus → String
  | .kernelDecided => "kernel_decided"
  | .hypothesis => "hypothesis"

/-- Report §8.4.2, §8.4.4, §9.5.3 — the certificate record, schema v1.0.0. -/
structure Certificate where
  pattern : String
  /-- the instance `(n, M, r)` -/
  n : Nat
  M : Nat
  r : Nat
  /-- the specification: `ε` (discrete case, 0), `δ` exact -/
  epsilon : Rat
  delta : Rat
  /-- the measured grade of the emitted circuit -/
  grade : Grade
  hypotheses : List String
  restoration : String
  predicateHash : String
  circuitHash : String
  /-- Stage 8b -/
  proofHash : Option String
  /-- the noisy operations counted by `G` of `δ_hw ≤ δ + G·p̄` (§3.3.3) -/
  gateCounts : GateCounts
  config : RefConfig
  /-- Stage 8b: the axioms of the certificate theorem (`#print axioms`) -/
  axioms : List String
  status : Status
  /-- Stage 8b: the fully qualified name of the kernel-checked theorem -/
  theoremName : Option String
  /-- Stage 8b: the tracked obligations (`status = withObligations`) -/
  obligations : List String
  /-- Stage 9b: the declared front-end boundary (`FrontEndCheck.trustText`) -/
  frontEnd : String
  /-- Stage 11b: the check against a declared hardware profile (`--profile`) -/
  hardware : Option HardwareCheck := none
  /-- Stage 12d: the diffusion, written only when it is not the tree (`diffusion_shape`) -/
  diffusion : CertDiffusion := .tree
  /-- Stage 14a: how `M` was obtained (`solution_count.status`) -/
  count : CountStatus := .hypothesis
  deriving Repr

/-- The schema version written to `schema_version` (semver): "1.6.0" for every certificate
since Stage 14a (the object `solution_count` is required; `hardware`, Stage 11b, and
`diffusion_shape`, Stage 12d, are optional under it). Before Stage 14a the version depended on
the optional objects present (1.3.0 / 1.4.0 / 1.5.0) to keep older certificates byte-identical;
Stage 14a regenerates all three committed certificates, so one version suffices. -/
def schemaVersion : String := "1.6.0"

/-- The trust-boundary note of the `hardware` object (§5.3.1). -/
def hardwareNote : String :=
  "routing, native gates and calibration are outside the trust boundary"

/-- Report §3.3.2–3.3.3, §9.5.3 — the `hardware` object (schema v1.4.0). -/
def hardwareJson (h : HardwareCheck) : Json :=
  let ratOpt : Option Rat → Json := fun | some q => Json.str (toString q) | none => Json.null
  Json.mkObj
    [("profile", Json.str h.profile), ("profile_hash", Json.str h.profileHash),
     ("components", Json.mkObj (h.components.map fun c => (c.key, Json.mkObj
        [("required", c.required),
         ("budget", match c.budget with | some b => b | none => Json.null),
         ("fits", Json.bool c.fits)]))),
     ("fits", Json.bool h.fits), ("G", h.G), ("p_bar", ratOpt h.pBar),
     ("delta_hw", ratOpt h.deltaHw),
     ("vacuous", match h.vacuous with | some v => Json.bool v | none => Json.null),
     ("note", Json.str hardwareNote)]

/-- Report §9.5.3 — the JSON envelope (`docs/certificate.schema.json`). -/
def Certificate.toJson (c : Certificate) : Json :=
  let str (s : String) : Json := Json.str s
  let ratStr (q : Rat) : Json := Json.str (toString q)
  let optStr : Option String → Json := fun | some s => str s | none => Json.null
  Json.mkObj <|
    [("schema_version", str schemaVersion),
     ("pattern", str c.pattern),
     ("instance", Json.mkObj [("n", c.n), ("M", c.M), ("r", c.r)]),
     ("solution_count", Json.mkObj [("value", c.M), ("status", str c.count.name)]),
     ("spec", Json.mkObj [("epsilon", ratStr c.epsilon), ("delta", ratStr c.delta),
       ("success_probability", ratStr (1 - c.delta))]),
     ("grade", Json.mkObj [("w", c.grade.w), ("d", c.grade.d), ("t", c.grade.t),
       ("a", c.grade.a)]),
     ("hypotheses", Json.arr (c.hypotheses.map str).toArray),
     ("restoration", str c.restoration),
     ("hashes", Json.mkObj [("predicate", str c.predicateHash), ("circuit", str c.circuitHash),
       ("proof", match c.proofHash with | some h => str h | none => Json.null)]),
     ("trust_boundary", Json.mkObj [("emitted", str "QIR text"),
       ("profile", str "adaptive_profile"),
       ("emitter", str "unverified; translation-validated by re-parse"),
       ("front_end", str c.frontEnd)]),
     ("hardware_perturbation", Json.mkObj [("formula", str "δ_hw ≤ δ + G·p̄"),
       ("G", c.gateCounts.total), ("p_bar", str "profile parameter"),
       ("counts", Json.mkObj [("unitary", c.gateCounts.unitary),
         ("mid_circuit_measurements", c.gateCounts.midCircuitMeasurements),
         ("classically_controlled", c.gateCounts.classicallyControlled),
         ("terminal_measurements", c.gateCounts.terminalMeasurements)])]),
     ("reference_configuration", Json.mkObj [("lean", str c.config.lean),
       ("mathlib", str c.config.mathlib), ("physlib", str c.config.physlib),
       ("cpu", optStr c.config.cpu),
       ("logical_cpus", match c.config.logicalCpus with | some k => k | none => Json.null),
       ("clock", optStr c.config.clock), ("lean_threads", optStr c.config.leanThreads),
       ("kernel_check", match c.config.kernelCheck with
         | some k => Json.mkObj [("wall_ms", k.wallMs),
             ("kernel_ms", match k.kernelMs with | some m => m | none => Json.null),
             ("runs", k.runs), ("statistic", str k.statistic)]
         | none => Json.null)]),
     ("theorem", optStr c.theoremName),
     ("axioms", Json.arr (c.axioms.map str).toArray),
     ("obligations", Json.arr (c.obligations.map str).toArray),
     ("status", str c.status.name)] ++
    (c.hardware.map fun h => [("hardware", hardwareJson h)]).getD [] ++
    (if c.diffusion != .tree then [("diffusion_shape", str c.diffusion.name)] else [])

/-- Report §6.2.4, §6.3.2 — the restoration conjunct as stated in the certificate. -/
def restorationText : String := "AncRestore: all ancillae |0…0⟩ on density operators"

/-- Report §8.4.2 — the certificate of a matched Grover instance from (source text, extracted
signature, match, circuit, grade, `r`, `n`, `M`, exact `δ`). Checks that the data agree: the
signature's arity and solution count are `n` and `M`, the circuit has `n` data qubits, and the
grade is the circuit's measured grade (DECISIONS.md, Stage 5b review). `frontEnd` is the
declared front-end boundary (`FrontEndCheck.trustText` of the Stage 9b validation). `count`
(Stage 14a) says whether `M` is decided by the kernel (`hM_count`) or a hypothesis (`hM_card`);
only in the second case is it listed under `hypotheses`. -/
def Certificate.build (src : String) (sig : SigmaIn) (entry : LibEntry) (facts : List Discharged)
    (C : Circuit) (g : Grade) (r n M : Nat) (δ : Rat) (cfg : RefConfig) (frontEnd : String)
    (count : CountStatus := .hypothesis) : Except String Certificate := do
  if sig.arity != n then throw s!"arity {sig.arity} of the signature ≠ n = {n}"
  if sig.solutionCount != some M then throw s!"solution count of the signature ≠ M = {M}"
  if C.nData != n then throw s!"the circuit has {C.nData} data qubits, n = {n}"
  if g != C.grade then throw "the grade is not the measured grade of the circuit"
  let (hP, hC, G) := (Certify.predicateHash src, Certify.circuitHash C, Certify.gateCounts C)
  return {
    pattern := entry.name, n, M, r, epsilon := 0, delta := δ, grade := g
    hypotheses :=
      (match count with
        | .hypothesis => [s!"solution_count = {M} (hM_card, supplied, not decided)"]
        | .kernelDecided => []) ++
      facts.map (fun d => s!"{d.cond.render}: {d.render} (side condition of {entry.name}, \
        discharged by the matcher)") ++
      [s!"iterations r = {r} (parameter of grover_parametric_lemma; δ is exact for this r)"]
    restoration := restorationText
    predicateHash := hP, circuitHash := hC, proofHash := none
    gateCounts := G, config := cfg, axioms := [], status := .notYetAudited, theoremName := none,
    obligations := [], frontEnd, count }

/-! ## The matched Grover instance (shared by `cqr emit` and the certificate) -/

/-- Report §4.2.4, §8 — the matched Grover instance of a predicate: the library entry and its
discharged side conditions, the network, `n`, `M`, `r`, the oracle and the Grover circuit. -/
structure GroverInstance where
  entry : LibEntry
  facts : List Discharged
  net : Network
  n : Nat
  M : Option Nat
  r : Nat
  oracle : Circuit
  circuit : Circuit
  /-- Stage 12d: the diffusion of `circuit` -/
  diffusion : CertDiffusion := .tree

/-- Why no Grover instance was built: a diagnostic (front end, match, synthesis), or a usage
error (no `r` and no `M` to compute `r⋆`). -/
inductive InstanceError where
  | diagnostic (d : Diagnostic)
  | usage (msg : String)

/-- Report §4.2.4, §8 — match the signature against the library (it must match `Grover`), then
synthesize the oracle and the Grover circuit with `r` iterations (default `r⋆` from `M`, in
`Float`: it only chooses `r`). `sig` already carries `--solutions`. Stage 12d: with
`diff = .fewLog` the circuit is `groverCircuitFew N n r .logDepth` (candidate B). -/
def groverInstance (tp : TypedProgram) (sig : SigmaIn) (iters : Option Nat)
    (diff : CertDiffusion := .tree) : Except InstanceError GroverInstance := do
  let (entry, facts) ← match matchLibrary library sig.toTerm.normalize with
    | .matched e _ ds => pure (e, ds)
    | _ => throw (.diagnostic (Diagnostic.at .matching .noMatchingPattern ⟨1, 1⟩
        "no library pattern matches (run `cqr match` for the repair hint)"))
  if entry.name != "Grover" then
    throw (.usage s!"matched pattern {entry.name}: only Grover is emitted (report §8)")
  let n := sig.arity
  let some r := iters <|> sig.solutionCount.bind (rStar n)
    | throw (.usage s!"give --iterations r, or a solution count M with 1 ≤ M ≤ 2^{n} \
        (from ℰ or --solutions M) to compute r⋆")
  let res : Except Diagnostic (Network × Circuit × Circuit) := do
    let N ← toNetwork tp
    let o ← synthesizeOracle N
    let C ← match diff with
      | .tree => groverCircuit N n r
      | .fewLog => groverCircuitFew N n r .logDepth
    return (N, o, C)
  match res with
  | .error d => throw (.diagnostic d)
  | .ok (N, o, C) => return { entry, facts, net := N, n, M := sig.solutionCount, r, oracle := o,
                               circuit := C, diffusion := diff }

/-- Report §8.4.2 — the Stage 8a certificate of a source text (no kernel check, no audit):
front end, ℰ, match, synthesis at `r` (default `r⋆`), exact `δ`, and (Stage 9b) the front-end
validation, whose mismatch is an error. -/
def certificateOf (src : String) (cfg : RefConfig) (iters : Option Nat := none) :
    Except String Certificate := do
  let tp ← (parse src >>= check).mapError (·.message)
  let sig := extract tp
  let gi ← (groverInstance tp sig iters).mapError fun
    | .diagnostic d => d.message
    | .usage m => m
  let some M := gi.M | throw "the certificate needs the solution count M"
  let fe := validateFrontEnd tp gi.net gi.n
  let some feText := fe.trustText
    | throw ((fe.diagnostic? tp.name ⟨1, 1⟩).map (·.message) |>.getD "front-end validation")
  Certificate.build src sig gi.entry gi.facts gi.circuit gi.circuit.grade gi.r gi.n M
    (groverDelta gi.r gi.n M) cfg feText

end CQRV.Certify

end
