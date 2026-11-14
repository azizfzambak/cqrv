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
review, item 4): 1a the parser, the surface checker and (Stage 16b) the typed-term printer
(declared trust boundary) and 1b the typed AST → network translation (kernel-checked since
Stage 16b: `front_end` of `Cert.lean` from `toNetwork_pred`; exhaustively validated on 2ⁿ inputs
in Stages 9b–16a). With `--profile` (Stage 11b, decision 2 of
the tasks) a last row "Hardware profile" reports the check against the declared profile, with
its own status `checked against declared profile (not a proof about hardware)`; without it the
report is unchanged. Stage 14a: the header and the stage-2 note say whether `M` is decided by
the kernel (`hM_count`) or the hypothesis `hM_card` (`RunData.count`). Stage 17b (PHASE2_SPEC.md
§A.1, §A.8.2): row 4 also prints the second record `GradeExt` (`ext: 2Q, T-depth, rot, meas, ff`,
measured, `gradeExt_eq`), its note adds the rotation sentence only when `rot > 0`, and row 8's
note says that QIR `p` is `rz` up to a global phase.
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
  /-- Stage 14a: how `M` was obtained -/
  count : CountStatus := .hypothesis
  /-- Stage 15b: the uncomputation mode of `oracle` and `circuit` -/
  uncompute : UncomputeMode := .mbu
  /-- Stage 21a4: extra rows after Table 8.5.2 (the certified selection), none by default -/
  extraRows : List ReportRow := []
  /-- Stage 21a4: extra header lines after the instance line, none by default -/
  extraHeader : List String := []
  deriving Inhabited

/-- `(w, d, t, a)` -/
def gradeText (g : Grade) : String := s!"(w, d, t, a) = ({g.w}, {g.d}, {g.t}, {g.a})"

/-- PHASE2_SPEC.md §A.1 (Stage 17b) — the second record in row 4. -/
def gradeExtText (e : GradeExt) : String :=
  s!"ext: 2Q {e.twoQ}, T-depth {e.tDepth}, rot {e.rot}, meas {e.meas}, ff {e.ff}"

/-- PHASE2_SPEC.md §A.8.2 (amended 2026-10-31) — the rotation note, only when `rot > 0`. -/
def rotNote (e : GradeExt) : String :=
  if e.rot > 0 then
    "; Clifford+T cost of the rotation gates depends on the synthesis precision (PHASE2_SPEC §C), \
      not folded into t"
  else ""

/-- Report §8.2 (Stage 14a) — the trust-boundary clause for `M` in the stage-2 note. -/
def countNote (n : Nat) : CountStatus → String
  | .hypothesis => "M is the hypothesis hM_card, never decided"
  | .kernelDecided => s!"M is decided by the kernel (hM_count: Network.countSat on all 2^{n} \
      inputs, Network.countSat_eq_card)"

/-- The word after `M = …` in the report header. -/
def countWord : CountStatus → String
  | .hypothesis => "hypothesis"
  | .kernelDecided => "kernel-decided"

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
  -- Stage 16b: the typed AST → network step is a theorem of Cert.lean (`front_end`), kernel-checked
  let feRow : Verification × String × String :=
    (.kernelChecked,
     s!"n = {d.n} input bits; `front_end` covers all 2^{d.n} = {2 ^ d.n} inputs (a theorem, not \
      an enumeration)",
     s!"typed AST → network: proved (`toNetwork_pred`, Stage 16a) and kernel-checked at this \
      instance in Cert.lean — `prog` (the typed-term literal), `prog_scoped` (decide), \
      `net_ok : toNetwork prog = .ok net` (decide +kernel), `front_end : ∀ x, evalProgram prog x \
      = Network.pred net {d.n} x`; the literal printer is unverified (a wrong literal gives a \
      different network and fails net_ok); declared as \
      trust_boundary.front_end = \"{frontEndProvedText}\"")
  let kms := match d.timing.kernelMs with | some k => s!"kernel {msText k}, " | none => ""
  [ { stage := "1a. DSL Input: parser, surface checker",
      input := s!"{d.source} (predicate_hash {d.predicateHash.take 12}…)",
      output := s!"Typed AST `{d.name}`",
      verification := .declaredTrustBoundary, resources := "—",
      note := "parser, surface checker and the typed-term printer: declared trust boundary (the \
        theorem of 1b starts at the typed-term literal `prog` of Cert.lean, so an error before it \
        is not detected there); the source text is bound by predicate_hash only" },
    { stage := "1b. DSL Input: typed AST → network", input := s!"Typed AST `{d.name}`",
      output := "Boolean network (toNetwork)",
      verification := feRow.1, resources := feRow.2.1, note := feRow.2.2 },
    { stage := "2. Spec Extraction", input := "Typed AST",
      output := s!"Ground signature σ_in: {d.sig.problemClass.name}, n = {d.sig.arity}, M = {m}, \
        iter = {match d.sig.iter with | .bounded k => s!"bounded({k})" | .unbounded => "unbounded"}",
      verification := .unverified,
      resources := s!"ĉ∧ = {d.sig.andComplexity} (upper bound), AND-depth {d.sig.andDepth}, \
        ancilla budget {d.sig.ancillaBudget}",
      note := s!"ℰ is total but not proved correct; the certificate theorem does not use σ_in \
        (Cert.lean restates n, M and the network); {countNote d.n d.count}" },
    { stage := "3. Pattern Matching", input := "Signature σ_in",
      output := s!"{d.pattern}: σ = {"{"}{d.subst}{"}"}",
      verification := .unverified,
      resources := s!"side conditions discharged: {if d.sides.isEmpty then "none" else
        "; ".intercalate d.sides}",
      note := "Algorithm 1 (Miller pattern); `millerMatch_sound` is proved for the algorithm, \
        this run is not kernel-checked; the certificate theorem states the Grover instance \
        directly" },
    { stage := "4. QPLP Instant.",
      input := s!"QPLP {d.pattern} + σ, r = {d.r}, uncompute = {d.uncompute}",
      output := s!"Concrete circuit H^⊗{d.n} · (U_s U_P)^{d.r} (`emitted` in Cert.lean)",
      verification := .kernelChecked,
      resources := s!"grade {gradeText d.circuit.grade} (measured); δ = {d.delta} exact; \
        {gradeExtText d.circuit.gradeExt} (measured)",
      note := s!"emitted_ok (hash link: synthesizer output = IR literal), grade_eq, gradeExt_eq, \
        nAnc_eq, delta_eq by `decide +kernel` in Cert.lean; δ = 1 − sin²((2r+1)θ) via \
        sin_sq_odd_mul{rotNote d.circuit.gradeExt}" },
    { stage := "5. Oracle Synthesis",
      input := s!"Boolean network ({d.net.nodes.size} nodes, {andNodes} AND)",
      output := match d.uncompute with
        | .mbu => "U_P + proof (Lemma 6.3.2, lemma_6_3_2_xor_of_le)"
        | .coherent => "U_P + proof (Lemma 6.3.2 in mode coherent, lemma_6_3_2_coherent_of_le)",
      verification := .kernelChecked,
      resources := s!"oracle {gradeText d.oracle.grade}; {andNodes} AND nodes vs ĉ∧ = \
        {d.sig.andComplexity}",
      note := match d.uncompute with
        | .mbu => "OracleCert of the network literal: synthesizeOracle net = .ok … and C.WF by \
            `decide +kernel`; restoration by lemma_6_3_2_xor_of_le"
        | .coherent => "OracleCertCoh of the network literal: synthesizeOracle net .coherent = \
            .ok … and C.WF by `decide +kernel`; restoration by lemma_6_3_2_coherent_of_le \
            (PHASE2_SPEC.md §A.0.1: every AND undone by the adjoint of its compute block, no \
            measurement, no classical bit)" },
    { stage := "6. Ancilla Restore", input := "Oracle U_P and diffusion MCZ",
      output := "Restored circuit (AncRestore conjunct of `cert`)",
      verification := .kernelChecked,
      resources := s!"T after the first measurement: oracle {tAfterFirstMeasure d.oracle}, \
        diffusion {tAfterFirstMeasure d.diffusion}; {G.midCircuitMeasurements} MBU measurements, \
        {G.classicallyControlled} classically controlled gates; a = {d.circuit.grade.a}",
      note := match d.diffusionShape, d.uncompute with
        | .tree, .coherent => "AncRestore n a emitted (groverOp P ^ r * hadamardU n), on density \
            operators (Lemma 6.3.2 in mode coherent per oracle call and for the MCZ of the tree \
            diffusion, certified from the circuit: grover_certificate_coherent)"
        | .tree, _ => "AncRestore n a emitted (groverOp P ^ r * hadamardU n), on density operators \
            (Lemma 6.3.2 per oracle call, DiffusionCert for the MCZ)"
        | .fewLog, _ => "AncRestore n a emitted (groverOp P ^ r * hadamardU n), on density \
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
        (check_emit.sh, certify_check.py), not in this run; trust_boundary.emitted = QIR text; \
        a phase gate p is emitted to QIR as rz with a hex-float angle, rz(θ) = e^(−iθ/2)·p(θ): a \
        global phase per gate (per branch under ifBit), irrelevant to every statement of the \
        certificate; a top-level cp is its five-gate decomposition (decomposeCp_unitary_wf)" } ]

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
  d.rows ++ d.extraRows ++ (d.hardware.map fun h => [hardwareRow h]).getD []

/-- A Markdown table cell (`|` escaped, no newlines). -/
def mdCell (s : String) : String := (s.replace "|" "\\|").replace "\n" " "

/-- Report §8.5.2 — the run report as Markdown: status line, Table 8.5.2, notes. -/
def RunData.toMarkdown (d : RunData) : String :=
  let rows := d.allRows
  let header := s!"# Run report: {d.name}\n\n\
    Report §8.5.2 (Table 8.5.2 shape), Stage 9b decision 4: every resource is a measured value \
    of this run, never a report target.\n\n\
    - source: `{d.source}`\n- instance: n = {d.n}, M = {d.M} ({countWord d.count}), r = {d.r}, \
    uncompute = {d.uncompute}\n\
    {String.join (d.extraHeader.map fun l => s!"- {l}\n")}\
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
