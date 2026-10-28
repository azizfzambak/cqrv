module

public import Lean.Data.Json
public import CQRV.Certify.Certificate

/-!
# CQRV.Certify.RunReport

Report §8.5.2 (Table 8.5.2, pipeline stage results), §8.5.1, §9.5.1 — the run report of
`cqr certify … --report` (Stage 9b, reviewer decision 4; DECISIONS.md 2026-10-25): one row per
pipeline stage in the shape of Table 8.5.2 (stage, input, output, verification, resources), with
the verification status one of `kernel-checked`, `exhaustively validated`, `declared trust
boundary`, `unverified`, and **measured** resources only (never the report's targets). Every
number is computed from the run's own objects: the signature, the network, the synthesized
circuits, the kernel-check timing and the audit. Each row also carries a note saying what the
status covers; the Markdown file lists the notes under the table. Stage 1 has two rows (Stage 9b
review, item 4): 1a the parser and surface checker (declared trust boundary, shared by both sides
of the front-end comparison) and 1b the typed AST → network translation (exhaustively validated
on 2ⁿ inputs; declared trust boundary for n > 16). With `--profile` (Stage 11b, decision 2 of
the tasks) a last row "Hardware profile" reports the check against the declared profile, with
its own status `checked against declared profile (not a proof about hardware)`; without it the
report is unchanged.
-/

@[expose] public section

namespace CQRV.Certify

open Lean CQRV.DSL CQRV.Matching CQRV.Synthesis

/-- Report §8.5.2 — verification status of a pipeline stage (decision 4). -/
inductive Verification where
  | kernelChecked
  | exhaustivelyValidated
  | declaredTrustBoundary
  | unverified
  /-- Stage 11b: the grade and δ_hw against a declared hardware profile -/
  | checkedAgainstProfile
  deriving Repr, DecidableEq, Inhabited

/-- The words of decision 4. -/
def Verification.name : Verification → String
  | .kernelChecked => "kernel-checked"
  | .exhaustivelyValidated => "exhaustively validated"
  | .declaredTrustBoundary => "declared trust boundary"
  | .unverified => "unverified"
  | .checkedAgainstProfile => "checked against declared profile (not a proof about hardware)"

/-- Report §8.5.2 — one row of Table 8.5.2, plus what the status covers (`note`). -/
structure ReportRow where
  stage : String
  input : String
  output : String
  verification : Verification
  resources : String
  note : String
  deriving Repr, Inhabited

/-- Report §8.5.1–8.5.2 — the data of one `cqr certify` run that the report is built from. -/
structure RunData where
  name : String
  source : String
  predicateHash : String
  sig : SigmaIn
  pattern : String
  /-- the substitution, rendered `F₁ ↦ 6, …` -/
  subst : String
  /-- the discharged side conditions, rendered -/
  sides : List String
  net : Network
  oracle : Circuit
  diffusion : Circuit
  circuit : Circuit
  n : Nat
  M : Nat
  r : Nat
  delta : Rat
  frontEnd : FrontEndCheck
  theoremName : String
  certPath : String
  timing : KernelTiming
  axioms : List String
  statusLine : String
  certified : Bool
  /-- Stage 11b: the check against `--profile` -/
  hardware : Option HardwareCheck := none
  /-- Stage 12d: the diffusion of `circuit` (`--shape few:log`) -/
  diffusionShape : CertDiffusion := .tree
  deriving Inhabited

/-- `(w, d, t, a)` -/
def gradeText (g : Grade) : String := s!"(w, d, t, a) = ({g.w}, {g.d}, {g.t}, {g.a})"

/-- Report §6.2.2 — T gates of a circuit after its first mid-circuit measurement: for a
synthesized oracle (all compute blocks, then the phase flip, then every MBU block), the T-count of
the uncomputation. -/
def tAfterFirstMeasure (C : Circuit) : Nat :=
  (C.gates.dropWhile fun g => match g with | .measure _ _ => false | _ => true).foldl
    (· + ·.tCount) 0

/-- Milliseconds as seconds with two decimals. -/
def msText (ms : Nat) : String :=
  let c := (ms + 5) / 10
  s!"{c / 100}.{if c % 100 < 10 then "0" else ""}{c % 100} s"

/-- Report §8.5.2 — the rows of Table 8.5.2 for a run, stage 1 split into 1a / 1b (Stage 9b
review, item 4), measured values only. -/
def RunData.rows (d : RunData) : List ReportRow :=
  let G := gateCounts d.circuit
  let andNodes := d.net.andCount
  let m := match d.sig.solutionCount with | some m => s!"{m}" | none => "unknown"
  let feRow : Verification × String × String := match d.frontEnd with
    | .validated n =>
      (.exhaustivelyValidated, s!"n = {n} input bits; 2^{n} = {2 ^ n} inputs compared, 0 disagree",
       s!"typed AST → network: exhaustively validated (2^{n} inputs), `evalProgram` (reference \
        evaluator) vs `Network.pred (toNetwork …)` on every input; both are unverified Lean \
        code and the check is not kernel-checked; declared as \
        trust_boundary.front_end = \"{frontEndValidatedText n}\"")
    | .tooLarge n =>
      (.declaredTrustBoundary, s!"n = {n} input bits (> {frontEndLimit}: not enumerated)",
       s!"trust_boundary.front_end = \"{frontEndTrust}\"")
    | _ => (.unverified, "—", "no validation outcome")
  let kms := match d.timing.kernelMs with | some k => s!"kernel {msText k}, " | none => ""
  [ { stage := "1a. DSL Input: parser, surface checker",
      input := s!"{d.source} (predicate_hash {d.predicateHash.take 12}…)",
      output := s!"Typed AST `{d.name}`",
      verification := .declaredTrustBoundary, resources := "—",
      note := "parser and surface checker: declared trust boundary (shared by both sides of the \
        comparison in 1b, so 1b cannot detect their errors); the source text is bound by \
        predicate_hash only" },
    { stage := "1b. DSL Input: typed AST → network", input := s!"Typed AST `{d.name}`",
      output := "Boolean network (toNetwork)",
      verification := feRow.1, resources := feRow.2.1, note := feRow.2.2 },
    { stage := "2. Spec Extraction", input := "Typed AST",
      output := s!"Ground signature σ_in: {d.sig.problemClass.name}, n = {d.sig.arity}, M = {m}, \
        iter = {match d.sig.iter with | .bounded k => s!"bounded({k})" | .unbounded => "unbounded"}",
      verification := .unverified,
      resources := s!"ĉ∧ = {d.sig.andComplexity} (upper bound), AND-depth {d.sig.andDepth}, \
        ancilla budget {d.sig.ancillaBudget}",
      note := "ℰ is total but not proved correct; the certificate theorem does not use σ_in \
        (Cert.lean restates n, M and the network); M is the hypothesis hM_card, never decided" },
    { stage := "3. Pattern Matching", input := "Signature σ_in",
      output := s!"{d.pattern}: σ = {"{"}{d.subst}{"}"}",
      verification := .unverified,
      resources := s!"side conditions discharged: {if d.sides.isEmpty then "none" else
        "; ".intercalate d.sides}",
      note := "Algorithm 1 (Miller pattern); `millerMatch_sound` is proved for the algorithm, \
        this run is not kernel-checked; the certificate theorem states the Grover instance \
        directly" },
    { stage := "4. QPLP Instant.", input := s!"QPLP {d.pattern} + σ, r = {d.r}",
      output := s!"Concrete circuit H^⊗{d.n} · (U_s U_P)^{d.r} (`emitted` in Cert.lean)",
      verification := .kernelChecked,
      resources := s!"grade {gradeText d.circuit.grade} (measured); δ = {d.delta} exact",
      note := "emitted_ok (hash link: synthesizer output = IR literal), grade_eq, nAnc_eq, \
        delta_eq by `decide +kernel` in Cert.lean; δ = 1 − sin²((2r+1)θ) via sin_sq_odd_mul" },
    { stage := "5. Oracle Synthesis",
      input := s!"Boolean network ({d.net.nodes.size} nodes, {andNodes} AND)",
      output := "U_P + proof (Lemma 6.3.2, lemma_6_3_2_xor_of_le)",
      verification := .kernelChecked,
      resources := s!"oracle {gradeText d.oracle.grade}; {andNodes} AND nodes vs ĉ∧ = \
        {d.sig.andComplexity}",
      note := "OracleCert of the network literal: synthesizeOracle net = .ok … and C.WF by \
        `decide +kernel`; restoration by lemma_6_3_2_xor_of_le" },
    { stage := "6. Ancilla Restore", input := "Oracle U_P and diffusion MCZ",
      output := "Restored circuit (AncRestore conjunct of `cert`)",
      verification := .kernelChecked,
      resources := s!"T after the first measurement: oracle {tAfterFirstMeasure d.oracle}, \
        diffusion {tAfterFirstMeasure d.diffusion}; {G.midCircuitMeasurements} MBU measurements, \
        {G.classicallyControlled} classically controlled gates; a = {d.circuit.grade.a}",
      note := match d.diffusionShape with
        | .tree => "AncRestore n a emitted (groverOp P ^ r * hadamardU n), on density operators \
            (Lemma 6.3.2 per oracle call, DiffusionCert for the MCZ)"
        | .fewLog => "AncRestore n a emitted (groverOp P ^ r * hadamardU n), on density \
            operators (Lemma 6.3.2 per oracle call; few-ancilla MCZ by \
            mczFew_logDepth_ancRestore, KG Theorem 5.1 for every n, Stage 13a; no per-instance \
            classical check)" },
    { stage := "7. Certificate Gen", input := "Proof + grade",
      output := s!"{d.certPath}, certificate.json (theorem {d.theoremName})",
      verification := .kernelChecked,
      resources := s!"{kms}wall {msText d.timing.wallMs} ({d.timing.statistic}); axioms: \
        {", ".intercalate d.axioms}",
      note := s!"lake env lean exit 0; #print axioms audited; status: {d.statusLine}" },
    { stage := "8. QIR Export", input := "Internal circuit (`emitted`)",
      output := s!"QIR text ({d.name}.qir), OpenQASM 3 ({d.name}.qasm)",
      verification := .declaredTrustBoundary,
      resources := s!"G = {G.total} noisy operations ({G.unitary} unitary, \
        {G.midCircuitMeasurements} mid-circuit measurements, {G.classicallyControlled} \
        classically controlled, {G.terminalMeasurements} terminal measurements)",
      note := "emitter unverified; translation-validated by re-parse in tests/diff \
        (check_emit.sh, certify_check.py), not in this run; trust_boundary.emitted = QIR text" } ]

/-- Report §3.3.2–3.3.3 — the row "Hardware profile" (Stage 11b): per-component check and
`δ_hw`, from the run's grade, `δ` and `G`. -/
def hardwareRow (h : HardwareCheck) : ReportRow :=
  let comp := "; ".intercalate (h.components.map fun c =>
    match c.budget with
    | some b => s!"{c.name} {c.required} / {b}: {if c.fits then "fits" else "exceeds"}"
    | none => s!"{c.name} {c.required} / —: not limiting")
  { stage := "Hardware profile",
    input := s!"profile {h.profile} (profile_hash {h.profileHash.take 12}…), grade, δ, G",
    output := h.statusLine,
    verification := .checkedAgainstProfile,
    resources := s!"{comp}; G = {h.G}",
    note := s!"declared profile figures, not calibration data; {hardwareNote} (report §5.3.1); \
      not part of the certified status (the certificate is about the ideal channel)" }

/-- Report §8.5.2 — the rows of the run report: Table 8.5.2, then the hardware row if a
profile was given. -/
def RunData.allRows (d : RunData) : List ReportRow :=
  d.rows ++ (d.hardware.map fun h => [hardwareRow h]).getD []

/-- A Markdown table cell (`|` escaped, no newlines). -/
def mdCell (s : String) : String := (s.replace "|" "\\|").replace "\n" " "

/-- Report §8.5.2 — the run report as Markdown: status line, Table 8.5.2, notes. -/
def RunData.toMarkdown (d : RunData) : String :=
  let rows := d.allRows
  let header := s!"# Run report: {d.name}\n\n\
    Report §8.5.2 (Table 8.5.2 shape), Stage 9b decision 4: every resource is a measured value \
    of this run, never a report target.\n\n\
    - source: `{d.source}`\n- instance: n = {d.n}, M = {d.M} (hypothesis), r = {d.r}\n\
    - status: **{d.statusLine}**\n\n\
    | Stage | Input | Output | Verification | Resources |\n|---|---|---|---|---|\n"
  let body := String.join (rows.map fun r =>
    s!"| {mdCell r.stage} | {mdCell r.input} | {mdCell r.output} | {r.verification.name} | \
      {mdCell r.resources} |\n")
  let notes := String.join ((rows.zipIdx.map fun (r, i) => s!"{i + 1}. {r.note}\n"))
  header ++ body ++ "\nWhat each status covers:\n\n" ++ notes

/-- Report §8.5.2 — the run report as JSON (`rows` in stage order). -/
def RunData.toJson (d : RunData) : Json :=
  Json.mkObj
    [("name", Json.str d.name), ("source", Json.str d.source),
     ("instance", Json.mkObj [("n", d.n), ("M", d.M), ("r", d.r)]),
     ("status", Json.str d.statusLine), ("certified", Json.bool d.certified),
     ("rows", Json.arr (d.allRows.map fun r => Json.mkObj
        [("stage", Json.str r.stage), ("input", Json.str r.input), ("output", Json.str r.output),
         ("verification", Json.str r.verification.name), ("resources", Json.str r.resources),
         ("note", Json.str r.note)]).toArray)]

end CQRV.Certify

end
