module

public import CQRV.Certify.Basic

/-!
# CQRV.Patterns

Report §3.2–3.3 (the QPLP record, instantiation, grade evaluation), Definition 4.1; PHASE2_SPEC.md
§A.5 amendment (6), the **syntactic layer** of the QPLP record (Stage 21a3). The `cqr` closure is
Physlib-free (§A.8 item 6), so the record `QPLP` holds what the CLI needs: the library entry, the
*names* of the specification family, of the parametric lemma and of the semantic instance
(`QPLP.Sem`, `CQRV/Patterns/Sound.lean`, Physlib-side), the grade kind, and the builder dispatch
that replaces the Grover-only `groverInstance` as the entry point of `cqr certify`. The names are
checked against the environment by `tests/CQRVTests/Patterns.lean`.

`qplpLibrary.map (·.entry) = library` (`qplpLibrary_entries`), so Proposition 5.1
(`matchLibrary_spec`, Stage 21a2) applies unchanged: the matched entry is an entry of the library
and `Matches` holds for it (`matchLibrary_matched`), and `instantiate` dispatches on that entry.
-/

@[expose] public section

namespace CQRV.Patterns

open CQRV.DSL CQRV.Matching CQRV.Synthesis CQRV.Certify

/-- PHASE2_SPEC §A.5 amendments (5)–(7) — how a certificate's `grade` is obtained: measured by the
scheduler on the whole circuit (`grade_kind "measured"`, the Grover certificates), or the Stage 19a
composed bound over the blocks (`"composed_bound"`, the counting certificate). -/
inductive GradeKind where
  | measured
  | composedBound
  deriving Repr, DecidableEq, Inhabited

/-- The word of `grade_kind` (`docs/certificate.schema.json`, 1.10.0). -/
def GradeKind.name : GradeKind → String
  | .measured => "measured"
  | .composedBound => "composed_bound"

/-- The builder an entry dispatches to (`instantiate`). -/
inductive Builder where
  | grover
  | count
  deriving Repr, DecidableEq, Inhabited

/-- Report §3.2, Definition 4.1; PHASE2_SPEC §A.5 amendment (6) — the syntactic QPLP record: the
precondition part (`LibEntry`: φ and its side conditions), the fully qualified names of the
specification family `S`, of the parametric lemma `π` and of the semantic record instance
(`QPLP.Sem`), the grade kind, and the builder dispatch. -/
structure QPLP where
  entry : LibEntry
  /-- the specification family of Definition 4.1 -/
  specName : Lean.Name
  /-- the parametric lemma π -/
  lemmaName : Lean.Name
  /-- the `QPLP.Sem` instance (`CQRV/Patterns/Sound.lean`) -/
  semName : Lean.Name
  gradeKind : GradeKind
  builder : Builder
  deriving Repr, Inhabited

/-- Report §8.1–8.3 — Grover: `groverEntry`, `SearchSpec`, `grover_parametric_lemma`,
`groverSem`, the measured grade. -/
def groverQPLP : QPLP :=
  { entry := groverEntry, specName := `CQRV.Grover.SearchSpec,
    lemmaName := `CQRV.Grover.grover_parametric_lemma, semName := `CQRV.Patterns.groverSem,
    gradeKind := .measured, builder := .grover }

/-- PHASE2_SPEC §A.4–A.5 — Count: `countEntry`, `CountSpec`, `ae_parametric_lemma_mk`,
`countSem`, the composed bound. -/
def countQPLP : QPLP :=
  { entry := countEntry, specName := `CQRV.Grover.CountSpec,
    lemmaName := `CQRV.Grover.ae_parametric_lemma_mk, semName := `CQRV.Patterns.countSem,
    gradeKind := .composedBound, builder := .count }

/-- Report §4.2.4 — the QPLP library, in the order of `library`. -/
def qplpLibrary : List QPLP := [groverQPLP, countQPLP]

/-- The QPLP library projects to the matching library, so `matchLibrary_spec` applies unchanged. -/
theorem qplpLibrary_entries : qplpLibrary.map (·.entry) = library := rfl

/-- The QPLP record of a matched entry (by name: `LibEntry` has no decidable equality). -/
def QPLP.ofEntry (e : LibEntry) : Option QPLP := qplpLibrary.find? (·.entry.name == e.name)

/-- Report §3.3 — an instantiated pattern: the Grover instance of `groverInstance` (report §8),
or the counting request of `CountRequest.ofProgram` (PHASE2_SPEC §A.4). -/
inductive Instance where
  | grover (gi : GroverInstance)
  | count (q : CountRequest)

/-- Report §3.3, §4.2.4; PHASE2_SPEC §A.5 amendments (5)–(6) — **the builder dispatch**: from the
entry `matchLibrary` matched (`e ∈ library` by `matchLibrary_matched`) through `qplpLibrary` to the
instance. The Grover arm calls the unchanged `groverInstance` (which re-matches the signature, as
`cqr emit` does); the Count arm builds the network and calls `CountRequest.ofProgram` at the
request's precision `m`, mode `mode`, shape tree, deciding the solution count by `Network.countSat`
exactly when `0 < countLimit ∧ n ≤ countLimit` (amendment (5′): otherwise the count is not decided
and the certificate is `cert` only). A Count entry needs a counting request. -/
def instantiate (e : LibEntry) (tp : TypedProgram) (src : String) (sig : SigmaIn)
    (problem : Problem) (iters : Option Nat) (diff : CertDiffusion) (countLimit : Nat)
    (mode : UncomputeMode) : Except InstanceError Instance :=
  match QPLP.ofEntry e with
  | none => .error (.usage s!"matched pattern {e.name} has no QPLP record")
  | some q =>
    match q.builder with
    | .grover => (groverInstance tp sig iters diff mode).map .grover
    | .count => do
      let m ← match problem with
        | .count m => pure m
        | .search => throw (.usage "the Count entry needs a counting request \
            (--problem count --precision m)")
      let net ← (toNetwork tp).mapError .diagnostic
      if !net.wf then throw (.usage s!"the network of {tp.name} is not well formed")
      let decideCount := 0 < countLimit && sig.arity ≤ countLimit
      let r ← (CountRequest.ofProgram tp src net sig.arity m mode decideCount).mapError .usage
      return .count r

end CQRV.Patterns

end
