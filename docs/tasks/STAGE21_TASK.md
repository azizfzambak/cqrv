# Stage 21 — The second library entry and decidability (PHASE2_SPEC §A.5–A.6; milestone M3)

PHASE2_SPEC.md §A.5 and §A.6 — read "Amendments before Stage 21" first; it fixes the Count
signature term, the request, the formal statement of Proposition 5.1, the QPLP record, and the
scope of certified selection. Also read the "20b3 done" paragraph of §A.4 and its items for
Stage 21. Report: §3.2.1 (Definition 4.1), §4.1.1–4.1.4, §4.2.1 (Proposition 5.1), §4.2.4
(Algorithm 2), §4.3, §9.3.2. PHASE2_ROADMAP.md row 21.

Stage 21 is written as **21a**, the main stage, in four tasks of one commit each. Each task starts
after the reviewer accepts the previous one, from `main`:
- **21a1**, the request and the Count entry, is specified here;
- **21a2**, Proposition 5.1, is specified here;
- **21a3**, the QPLP record and `cqr certify --problem count`, is specified below (written at the
  21a2 review);
- **21a4**, certified selection, is specified below (written at the 21a3 review).

**21m**, the M3 close (the header fix and `docs/M3_REPORT.md`), is specified below (written at the
M3 review, PHASE2_SPEC §A.9). **21b**, the stretch of §A.7, was decided at the M3 review: 21b1 (a
feasibility probe), then 21b2; 21b1 is specified below (written at the 21m review), and 21b2
below it (written at the 21b1 review).

Precondition: Stage 20 complete; main = c2199db (the 20b3 review commit). `git switch -c
stage-21a1 main`. The 21a1 commit includes this file and the reviewer's edits to
`docs/PHASE2_SPEC.md` and `docs/PHASE2_ROADMAP.md`, all unedited. Untracked and not yours:
`docs/paper/`, `docs/cqrv_report_revised_v4.docx`. Windows: `LEAN_NUM_THREADS=4`.

The process is as in Stage 20:
- run `lake build` in the foreground;
- `scripts/ci_local.sh` and any Lean run longer than a few minutes go to the user's separate
  terminal, one Lean process at a time;
- before CI, run the harness scripts the way `ci_local.sh` runs them (`.venv/Scripts/python.exe
  -I`, stdout redirected to a file, no `-X utf8`);
- `scripts/cli_smoke.sh` contains literal carriage returns: patch it in binary mode, never by a
  text-mode rewrite;
- then "ready for CI", the reviewer's audit, the user's CI run, the commit, and the closing reply.

**Invariants of 21a1 and 21a2.**
- **Search outputs unchanged.** With `--problem search`, the default, every output of `cqr check`,
  `extract`, `match`, `synthesize`, `emit` and `certify` is byte-identical to main's. There is one
  exception: the "proved" non-match wording that 21a2 adds to the no-match output.
- **Nothing regenerated.** No certificate is regenerated, and no definition that a committed
  `Cert.lean` evaluates is edited.
- **The `cqr` closure stays Lean core + Mathlib** (§A.8 item 6). Every new module in
  `CQRV/DSL/` and `CQRV/Matching/` is Physlib-free.
- **No new CI step.** The pass mark stays **18 PASS, 0 FAIL, 4 n/a**.
- **No `sorry`.** It is not part of the acceptance of either task: if a lemma resists after a
  serious attempt, stop and ask.
- **False statements.** If a statement here is false, give the counterexample and the corrected
  form, as at 19b, and report it in (e).
- **Lemma names.** CLAUDE.md rule 2: confirm every lemma name before using it.

---

## 21a1 — The request and the Count entry (Physlib-free)

### D1. The request (`CQRV/DSL/Signature.lean`, `CQRV/Matching/Term.lean`)

- `ProblemClass` gains the constructor `count`, with name `"Count"`. The extractor ℰ never
  produces it: ℰ is unchanged.
- `SigmaIn` gains the field `precision : Option Nat := none`.
  - `SigmaIn.toJson` writes `"precision"` only when it is `some m`, so the search JSON is
    byte-identical.
  - Update every structure literal of `SigmaIn` in the tests that needs it.
- `inductive Problem | search | count (m : Nat)`, and `SigmaIn.withProblem : Problem → SigmaIn →
  SigmaIn`:
  - `search` is the identity;
  - `count m` sets `problemClass := .count` and `precision := some m`, whatever ℰ found.
  - A program that is not a predicate `Bool^n → Bool` then fails at the `P` field with a hint.
    That is intended: the class is the request's, the type is the program's.
- `SigmaIn.toTerm` appends `.nat m` as a seventh argument of `sig` exactly when
  `precision = some m`. A search term keeps its six arguments.
- `sigFields` gains `"m"`, at index 6.

### D2. The library (`CQRV/Matching/Library.lean`)

```
def F₅ : MVar := .f 5 .nat      -- the precision m
def F₆ : MVar := .f 6 .any      -- the solution count, unconstrained for Count
def phiCount : Term :=
  .const "sig"
    [.const "Count" [], .mvar F₁ [], .mvar F₆ [],
     .const "→" [.const "Bool^" [.mvar F₁ []], .const "Bool" []],
     .const "bounded" [.mvar F₃ []],
     .const "PhaseKickback" [.const "Multiplicative" [], .mvar F₄ []],
     .mvar F₅ []]
def countEntry : LibEntry :=
  { name := "Count", priority := 1, precondition := phiCount, sides := [.ge (.mvar F₅ []) (.nat 1)] }
def library : List LibEntry := [groverEntry, countEntry]
```

Neither `groverEntry`, `phiGrover` nor Algorithm 2 (`matchLibrary`, `nearMiss`, `looseAt`)
changes.

**Note added at the 21a1 stop (2026-11-13; §A.5 amendment (2), corrected).** One change to
`matchLibrary` is authorized: the nearest-miss candidates are only the entries whose
precondition has the term's root shape. The root shape is the same head and the same argument
count, not the class constant. When no entry has it, the candidates fall back to all entries.

Nothing else changes:
- the early exit on a match;
- `nearMiss`, `looseAt` and `distLt`;
- the printed `dist`.

Every six-field term then has Grover as its only candidate, so the search outputs are those of
Stage 4 by construction. The pre-existing guard `(hintsOf whileSrc).map (·.location) ==
["M", "iter"]` must pass unchanged.

F₆ is of sort `any`, so a Count request matches whether ℰ computed the count (`.nat M`) or not
(`unknown`). The counting certificate is universal in M, so the entry does not constrain it.

### D3. The CLI (`Apps/cqr/Main.lean`)

`cqr extract` and `cqr match` take `--problem search|count` and `--precision m`, in any order
with the existing flags. Two cases are refused with the usage message and exit 2:
- `--problem count` without `--precision`;
- `--precision` without `--problem count`.

`--solutions M` keeps its meaning (a value of σ_in) under both problems. No other subcommand gets
the flags in 21a1: `certify` with `--problem` stays a usage error until 21a3.

The usage text lists the new flags.

### D4. Tests

`tests/CQRVTests/Matching.lean` (`#guard`, `example`):
- `phiCount.normalize.isMillerPattern`, and the library's names and priorities;
- σ_in literals built with `withProblem (.count 4)`:
  - the predicate of grover_pred_037 matches Count, with F₁ ↦ 8, F₃ ↦ 1, F₄ ↦ [0, 3, 7],
    F₅ ↦ 4, F₆ ↦ 32 and the fact `4 ≥ 1`;
  - with the count unknown, it matches with F₆ ↦ `unknown`;
- with `iter := unbounded`, the nearest entry is Count, and the hint kind is `unboundedIter`;
- with `count 0`, the side condition F₅ ≥ 1 fails at location `m`;
- every existing search literal still matches Grover with the same substitution.

`scripts/cli_smoke.sh` (binary-mode patch; exit codes and substrings, as the file does today):
- `cqr extract examples/grover_pred_037.cqr --problem count --precision 4` gives
  `"problem_class": "Count"` and `"precision": 4` (the pretty-printed form, as the existing extract
  checks);
- `cqr match examples/grover_pred_037.cqr --problem count --precision 4`: exit 0, pattern Count,
  `4 ≥ 1`;
- `cqr match examples/search_or.cqr --problem count --precision 3`: exit 0, Count, with no
  `--solutions` needed. The search request on the same file still fails without it: that is the
  difference between the entries;
- `cqr match examples/search_while.cqr --problem count --precision 4 --text`: exit 1, the iter
  hint, pattern Count;
- `cqr match examples/grover_pred_037.cqr --problem count --precision 0`: exit 1, the side
  condition at `m`;
- the two usage errors of D3: exit 2.

Byte-identity of the search path: before the change, record the stdout and exit code of
`cqr extract` and `cqr match` (JSON and `--text`) on every `examples/*.cqr`, with and without
the `--solutions` values cli_smoke uses. Compare after the change: identical. Report the number
of runs compared.

### 21a1 Docs / Acceptance / Stop

Docs:
- one DECISIONS.md entry;
- `docs/PROJECT_STATUS.md`;
- README status line ("Stage 21a in progress").

Acceptance:
- `lake build` green and warning-free;
- CI 18 PASS, 0 FAIL, 4 n/a;
- the search path byte-identical;
- the cqr closure Lean + Mathlib.

Stop and ask in any of these cases:
- an existing search output changes;
- `matchLibrary` needs a change;
- the nearest entry for a Count request on `search_while` is not Count.

---

## 21a2 — Proposition 5.1 (`CQRV/Matching/Complete.lean`, new, Physlib-free)

**Notes added at the 21a1 review (2026-11-13).** 21a1 is accepted (9782199). Precondition for
21a2: main = the 21a1 review commit, and `git switch -c stage-21a2 main`.
- (i) `matchLibrary` now finds a match with `List.findSome?` over the priority-sorted entries,
  then runs the old scan `go` on the nearest-miss candidates. A proof of `matchLibrary_noMatch`
  goes through the `findSome?`-is-`none` lemma (confirm its current name with `#check`). It needs
  nothing about `go` or the root-shape filter, which chooses only the reported miss.
- (ii) The root-shape filter appears in no E2 statement. A lemma about which entry a near miss
  names is optional and not part of (i)–(iii).
- (iii) Both entries are in the fragment with uniform arity. The F₆ of φ_Count has sort `any`, so
  `Binding.WF` must accept an `unknown` body for it: `MSort.admits .any` is true.

The statements follow §A.5 amendment (4). Import the module from `CQRV.Matching.Basic`. The
proofs use Lean core and Mathlib list lemmas only.

### E1. Definitions

- `Term.Ground t := t.hasAnyMVar = false`.
- `uniformArity φ : Bool`: every metavariable name occurs in φ with one argument count. Then
  `MillerFragment φ := φ.isMillerPattern = true ∧ uniformArity φ = true`. Uniform arity is
  needed; the counterexample is in amendment (4).
- `arityIn φ m`: that count.
- `Binding.WF k s b`:
  - `b.arity = k`;
  - `b.body` has no metavariable;
  - every free bound variable of `b.body` is `< k`;
  - `s.admits b.body`.
- `Subst.WFFor φ σ`: every metavariable `m` of φ has `σ.lookup m = some b` with
  `b.WF (arityIn φ m) m.sort`.
- `SideCond.mvars`, and `SideCond.Holds σ (.ge l r) := ∃ a b, l.subst σ = .nat a ∧ r.subst σ =
  .nat b ∧ b ≤ a`.
- `Matches e t := ∃ σ, σ.WFFor φₑ ∧ φₑ.subst σ = t ∧ ∀ c ∈ e.sides, c.Holds σ`, with
  `φₑ := normalize e.precondition`.

### E2. Theorems

- `millerMatch_complete : MillerFragment φ → t.Ground → σ.WFFor φ → φ.subst σ = t →
  ∃ σ', millerMatch φ t = .ok σ'`. This is the converse of `millerMatch_sound`, by mutual
  induction with `matchAt` and `matchList`, through a compatibility invariant between the partial
  result and σ. The converse of the existing `rename_abstr` is the key lemma: for `is` Nodup and
  the free variables of `b` below `is.length`, `abstr (indexOf? is) (b.rename (is.getD · 0)) =
  some b`.
- `millerMatch_wf : MillerFragment φ → t.Ground → millerMatch φ t = .ok σ' → σ'.WFFor φ`: the
  matcher's own result is in the match set.
- `matchers_agree : MillerFragment φ → σ.WFFor φ → τ.WFFor φ → φ.subst σ = t → φ.subst τ = t →
  ∀ m ∈ φ.mvars, σ.lookup m = τ.lookup m`: the match set of one entry is a singleton.
- `matchPrecondition_complete`: under the hypotheses of `millerMatch_complete`, with
  `∀ c ∈ sides, c.mvars ⊆ φ.mvars` and `∀ c ∈ sides, c.Holds σ`, `matchPrecondition φ sides t`
  returns `.ok`. The side conditions agree because the bindings agree.
- `matchLibrary_noMatch : (∀ e ∈ lib, MillerFragment (normalize e.precondition) ∧
  ∀ c ∈ e.sides, c.mvars ⊆ (normalize e.precondition).mvars) → t.Ground → matchLibrary lib t is
  not .matched → ∀ e ∈ lib, ¬ Matches e t`; and `matchLibrary_matched`: a `.matched e σ ds` result
  gives `e ∈ lib`, `Matches e t` witnessed by σ itself, and the agreement of every well-formed
  matcher with σ on φₑ's metavariables.
- `library_fragment` (decide): both entries satisfy the hypothesis of `matchLibrary_noMatch`.
- `library_match_unique : ∀ e₁ ∈ library, ∀ e₂ ∈ library, Matches e₁ t → Matches e₂ t → e₁ = e₂`.
  Prove it from a general lemma: two patterns whose roots are `sig` with different rigid
  constants at argument 0, or different argument counts, are never both matched by one term.
- `SigmaIn.toTerm_ground : s.toTerm.normalize.Ground`, so the CLI's terms satisfy the hypothesis.
- `matchLibrary_spec` collects the above for the library and a ground `t`:
  - on `.matched e σ _`: `e ∈ library`, `Matches e t`, no other entry matches, and every
    well-formed matcher agrees with σ;
  - otherwise: no entry matches.

**This is Proposition 5.1 (i)–(ii) for the implemented fragment.** Part (iii), the cost bound,
is not formalized (amendment (4)).

### E3. The proved non-match in the output

On a non-match:
- `cqr match --text` ends with the line `No library entry matches (proved: Proposition 5.1,
  matchLibrary_spec).`;
- the JSON hint of `cqr match`, `cqr emit` and `cqr certify` gains `"non_match":"proved"`.

Only the no-match outputs change; list them in (a). Add the substring checks to cli_smoke.

### E4. Tests

`tests/CQRVTests/Matching.lean`:
- `#guard_msgs` on `#print axioms matchLibrary_spec` (at most `propext`, `Classical.choice`,
  `Quot.sound`);
- examples of `matchLibrary_spec` on two concrete signatures: one match and one non-match;
- the counterexample of amendment (4) as a `#guard`: `millerMatch` fails, and the substitution
  exists, so uniform arity is necessary.

### 21a2 Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry;
- `docs/PROJECT_STATUS.md`;
- `docs/M2_REPORT.md` is frozen: do not edit it.

Acceptance:
- `lake build` green;
- CI 18 PASS, 0 FAIL, 4 n/a;
- every E2 theorem proved, with no `sorry`;
- the axioms as in E4.

Stop and ask in any of these cases:
- a statement of E2 needs a hypothesis beyond fragment, ground, well-formed substitution, and
  side conditions over φ's metavariables (give the counterexample);
- the proofs pass about 1 200 lines;
- `millerMatch`, `assign` or `matchAt` would need a change. The theorems are about the existing
  algorithm.

---

## 21a3 — The QPLP record and `cqr certify --problem count` (written at the 21a2 review, 2026-11-13)

PHASE2_SPEC §A.5: amendments (5)–(7), and the refinements (5′) and (6′) after the "21a2 done"
paragraph. Precondition: main = the 21a2 review commit. `git switch -c stage-21a3 main`. The 21a3
commit includes the reviewer's edits to this file, `docs/PHASE2_SPEC.md` and
`docs/PHASE2_ROADMAP.md`, unedited.

**Notes from the 21a2 review.**
- (i) `matchLibrary_spec` stays applicable as long as `qplpLibrary.map (·.entry) = library`.
  The dispatch uses `matchLibrary_matched`: the entry is in the library, and `Matches` holds.
- (ii) In the kernel, rewrite with `library_mergeSort` before deciding anything about
  `matchLibrary library`.
- (iii) `countEntry` matches with M unknown (F₆ : any). So the refusal of M = 0 comes from the
  request, after the count is decided, not from the matcher.

**Invariants of 21a3.**
- **The five committed certificate directories.** Every `Cert.lean`, `.qir` and `.qasm` stays
  byte-identical. Each `certificate.json` changes only in:
  - `schema_version`, 1.9.0 → 1.10.0 for the four Grover certificates;
  - `grade_kind`, added as `"measured"` for Grover;
  - the machine fields of `reference_configuration`.

  Each `run_report.{md,json}` changes only in its timing and machine lines and, for the counting
  certificate, in the rows that now come from the actual match (pattern Count, σ, side facts).
- **Search outputs.** Every output of `cqr check`, `extract`, `match`, `synthesize` and `emit` on
  a search request stays byte-identical.
- **The `cqr` closure stays Lean core + Mathlib.** `CQRV/Patterns/Basic.lean` is Physlib-free.
  `CQRV/Patterns/Sound.lean` is Physlib-side and not imported by the CLI.
- **No existing theorem statement changes.**
- **No new CI step.** The pass mark stays 18 PASS, 0 FAIL, 4 n/a. Report the time of step 22
  before and after.

### F1. The syntactic record (`CQRV/Patterns/Basic.lean`, Physlib-free)

```
inductive GradeKind | measured | composedBound
structure QPLP where
  entry : LibEntry
  specName : Lean.Name     -- the specification family of Definition 4.1
  lemmaName : Lean.Name    -- the parametric lemma π
  semName : Lean.Name      -- the QPLP.Sem instance of F2
  gradeKind : GradeKind
def groverQPLP : QPLP   -- groverEntry, SearchSpec, grover_parametric_lemma, groverSem, measured
def countQPLP : QPLP    -- countEntry, CountSpec, ae_parametric_lemma_mk, countSem, composedBound
def qplpLibrary : List QPLP := [groverQPLP, countQPLP]
theorem qplpLibrary_entries : qplpLibrary.map (·.entry) = library := rfl
```

Then the dispatch: `instantiate`, from the matched entry to `Instance.grover (gi : GroverInstance)
| Instance.count (q : CountRequest)`. It goes through `qplpLibrary`. The Grover arm calls the
unchanged `groverInstance`; the Count arm calls `CountRequest.ofProgram`. Choose the exact
signature. The module imports what it needs from `CQRV.Certify` (no cycle: `CQRV.Certify` does
not import `CQRV.Patterns`), and `Apps/cqr/Main.lean` imports `CQRV.Patterns.Basic`. Use the
names in full; F5 checks that they exist.

### F2. The semantic record (`CQRV/Patterns/Sound.lean`, Physlib-side; imported by `CQRV.lean` only)

Definition 4.1 as a dependent record, with the uniform claim of (6′):

```
structure QPLP.Sem (Params : Type) where
  pre : Params → Prop
  nData : Params → ℕ
  Out : Params → Type
  [fin : ∀ p, Fintype (Out p)] [dec : ∀ p, DecidableEq (Out p)] [pm : ∀ p, PseudoMetricSpace (Out p)]
  spec : ∀ p, Spec Unit (Out p)
  povm : ∀ p, POVM (Out p) (Reg (nData p))
  circuit : Params → Except DSL.Diagnostic Circuit      -- the Physlib-free builder
  eps delta : Params → ℝ
  grade : Params → Circuit → Grade
  target : ∀ p, Matrix (Reg (nData p)) (Reg (nData p)) ℂ
  proof : ∀ p, pre p → ∀ C, circuit p = .ok C →
    Realizes (spec p) (povm p) (groverChannel (nData p) C) (eps p) (delta p) (grade p C) ∧
      AncRestore (nData p) C.nAnc C (target p)
```

**The discrete output.** `DiscreteOut α` is a type synonym with the discrete metric (distance 0
or 1). Its `Fintype` and `DecidableEq` come by `inferInstanceAs`. Before defining the
`MetricSpace` instance, confirm whether Mathlib already has a discrete metric to reuse (rule 2).
Prove `realizes_discrete_of_exact`: `RealizesExact S dec Φ δ g → Realizes (S at DiscreteOut)
(dec at DiscreteOut) Φ 0 δ g`, by `realizes_zero_iff`.

**The two instances.**
- `groverSem`, from `grover_parametric_lemma`:
  - `Params`: `gp : GroverParams`, `D : DiffusionCert gp.n`, `r`;
  - `circuit := groverCircuit gp.oracle.N gp.n r`;
  - `Out := DiscreteOut (Reg gp.n)`, `spec := SearchSpec gp.oracle.P`, `povm := basisPOVM gp.n`;
  - `eps := 0`, `delta := 1 − sin²((2r+1)θ)`, `grade := Synthesis.grade`;
  - `target := groverOp P ^ r * hadamardU n`.
- `countSem`, from `ae_parametric_lemma_mk`:
  - `Params`: `n, M, m`, the network and the proofs that lemma takes, `shape`, `mode`;
  - `circuit := countingCircuit N n m none shape mode`;
  - `Out := CountOut m (M/2^n)`, `spec := CountSpec`, `povm := countPOVM n m (M/2^n)`;
  - `eps := ae_eps (M/2^n) m`, `delta := ae_delta`, `grade := Synthesis.grade`;
  - `target := U_count P m none`.

`pre` holds the side conditions: `1 ≤ M` for Grover, `1 ≤ m ∧ 1 ≤ M` for Count. The structural
facts are in `Params`. Each proof field is exactly its lemma's conclusion, read through the
record. Neither parametric lemma is re-proved.

A certificate's composed bound `g ≥ Synthesis.grade C` is a consequence of the record by the
monotonicity of `Realizes` in the grade. State it as a corollary, `QPLP.Sem.realizes_of_le`.

### F3. `cqr certify --problem count --precision m` (`Apps/cqr/Main.lean`, `CQRV/Certify/CountCert.lean`)

**Flags and refusals.**
- The flags are `[--count-limit k] [--uncompute mbu|coherent] [--bench k] [--report]
  [--out dir]`. `--problem` and `--precision` are parsed as in 21a1.
- Refused with the usage message, exit 2:
  - `--problem count` without `--precision`;
  - with `--problem count`: `--solutions`, `--iterations`, `--profile`, and `--shape` other than
    tree.
- The default output directory is `certs/<name>_count`.

**The run.** Signature with `withProblem` → `matchLibrary` → `instantiate` → the counting
generator, in the order of `cqr certify` (a non-match prints the proved hint). Then:
- **n ≤ limit.** `M := countSat`. If M = 0, print a diagnostic (stage `hypothesis`, a new code
  `no_solutions`), exit 1, and write nothing. Otherwise, the 20b3 certificate.
- **n > limit.** (5′): no `hM_count` and no `cert_count` in `Cert.lean`; the JSON and status line
  of (5′); and the run report says that the count is not decided and that the JSON's ε is the
  maximum over a.
- **`--uncompute coherent`.** `CountRequest` gains `mode`, and `renderCountCert` writes it in place
  of the literal `.mbu`. `ae_parametric_lemma_mk` is generic in the mode. The JSON `uncompute`
  follows.
- **`--bench k`.** The median, as `cqr certify` computes it.
- **`--report`.** The counting run report. Its matching rows come from the actual match
  (pattern Count, the substitution, the discharged `F₅ ≥ 1`), not from the 20b3 text "not
  matched by the library before Stage 21".

`CertifyTool count-certify` is removed, with its usage line. Regenerate
`examples/certs/grover_pred_037_count` with `cqr certify examples/grover_pred_037.cqr --problem
count --precision 4 --report --out examples/certs/grover_pred_037_count`. The invariants say what
may change.

### F4. Version 1.10.0 everywhere (`CQRV/Certify/Certificate.lean`, `docs/certificate.schema.json`)

`Certificate.toJson` writes `schema_version "1.10.0"` and `grade_kind "measured"`. Regenerate
the four Grover directories with the flags `certify_check.py` uses for each, with `--report`, and
check the invariants. If a byte of a `Cert.lean`, `.qir` or `.qasm` changes, stop.

The schema:
- **1.10.0 admits both patterns.**
  - Grover under 1.10.0 requires `grade_kind: "measured"` and forbids `blocks`.
  - Count requires `grade_kind: "composed_bound"`. Its `solution_count.status` is
    `kernel_decided` (value a natural number, and `instance.M` that number) or `not_decided`
    (value `null`, and `instance.M` `null`).
  - `grade_kind` is allowed only under 1.10.0.
  - `hardware` and `diffusion_shape` stay allowed under 1.10.0 for Grover.
- **The descriptions.** The top-level `grade` description covers both kinds, and the
  description of v1.10.0 is updated.
- **Envelopes before 1.10.0** stay valid under their own versions.

`tests/diff/cert_schema.py`:
- every committed certificate validates;
- the 20b3 negative test "Grover under 1.10.0" becomes "Grover under 1.10.0 without
  `grade_kind`";
- new negatives:
  - Grover with `grade_kind "composed_bound"`;
  - Grover under 1.10.0 with `blocks`;
  - Count `not_decided` with a numeric value;
  - Count `kernel_decided` with value `null`;
  - Count `not_decided` with a numeric `instance.M`.

### F5. Checks and tests

**`tests/diff/certify_check.py`**, inside the existing step:
- **The counting section** now runs `cqr certify --problem count`, with every 20b3 check kept: two
  runs byte-identical, the committed directory, the replayed circuit hash, QASM / QIR, the
  composed grade, and the two negative kernel tests.
- **New checks:**
  - a coherent run, in a temporary directory, not committed: certified; `uncompute` coherent;
    the blocks' literals end in `.coherent`; the composed grade recomputed;
  - a not-decided run with `--count-limit 4`, in a temporary directory: certified with `cert`
    only, `solution_count` `not_decided`, and the ε approx = π/2^4 + π²/4^4;
  - M = 0 on a temporary unsatisfiable predicate (for example
    `fn none(x: Vec Bool 4) -> Bool { idx(x, 0) and not idx(x, 0) }`): exit 1, code
    `no_solutions`, no file written;
  - the usage refusals of F3: exit 2.
- **The Grover sections** expect 1.10.0 and `grade_kind "measured"`.

**Lean tests** (`tests/CQRVTests/Patterns.lean`, new; Physlib-side):
- `qplpLibrary_entries`;
- every `specName`, `lemmaName` and `semName` in `qplpLibrary` exists in the environment
  (`Lean.Environment.contains`, through a command that fails otherwise);
- `#guard_msgs` on `#print axioms groverSem` and `#print axioms countSem` (the standard three);
- one `example` that applies `countSem.proof` at the AND network of the 19c tests.

**`scripts/print_axioms.sh`**: unchanged, except that the counting certificate line still audits
`cert`, `cert_count` and `front_end` of the committed directory.

### 21a3 Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry;
- `docs/PROJECT_STATUS.md`;
- README: the status line, and any sentence that says the certificates are at 1.9.0.

Acceptance:
- `lake build` green;
- CI 18 PASS, 0 FAIL, 4 n/a;
- the invariants hold (list the changed fields per certificate directory);
- the axioms as in F5;
- every new negative test rejected.

Stop and ask in any of these cases:
- a byte of a committed `Cert.lean`, `.qir` or `.qasm` changes;
- `QPLP.Sem` cannot be stated with the uniform claim. Report it, and propose the per-instance
  fallback of (6);
- a parametric lemma would have to be re-proved, or a theorem statement changed;
- a Lean process above 8 GB, or a kernel check above 10 minutes;
- step 22 above 900 s. Report the times; do not trim checks.

## 21a4 — Certified selection (written at the 21a3 review, 2026-11-14)

PHASE2_SPEC §A.6: amendment (8) and its refinement (8′). Precondition: main = the 21a3 review
commit. Start with `git switch -c stage-21a4 main`. The reviewer's edits for 21a4 are committed
with the 21a3 review.

**Notes from the 21a3 review.**
- (i) Selection adds no library entry. It matches as `cqr certify` does. It then builds the
  three candidates of (8′) at the request's r (from `--iterations`, or r⋆ from M) and computes
  each candidate's grade by compiled evaluation.
- (ii) For `grover_pred_037`, `treeCoherent` is dominated by `treeMbu` (8′). It still appears in
  the candidate list, with its grade and `admissible`, and `selected` still covers it.
- (iii) The header line "generated by `CertifyTool count-certify`" stays. 21a4 changes no byte of
  a committed `Cert.lean`.
- (iv) Step 7 took 230 s at the 21a3 CI (124 s at 21a2) with no new check. Report its time. If it
  is again above 200 s, give the time per check of `cli_smoke.sh`; do not change the script for
  this.

**Invariants of 21a4.**
- **The five committed certificate directories** are neither regenerated nor edited.
  `cqr certify` without `--budget` writes byte-identical output, which step 22 checks.
- **Search outputs.** Every output of `cqr check`, `extract`, `match`, `synthesize` and `emit`
  stays byte-identical. Re-run the 126-run comparison.
- **The `cqr` closure stays Lean core + Mathlib.** The selection module is Physlib-free.
- **No existing theorem statement changes.**
- **One new CI step.** The pass mark becomes 19 PASS, 0 FAIL, 4 n/a.

### G1. The selection (`CQRV/Patterns/Select.lean`, new, Physlib-free)

```
inductive Pref | width | depth | t | anc                 -- `--prefer`
def Grade.key (p : Pref) (g : Grade) : List ℕ           -- the preferred component, then the others in (w, d, t, a)
lexLt                                                   -- strict lexicographic order on keys
inductive Candidate | treeMbu | treeCoherent | fewLogMbu
def candidates : List Candidate := [.treeMbu, .treeCoherent, .fewLogMbu]
def Candidate.shape : Candidate → CertDiffusion
def Candidate.mode : Candidate → UncomputeMode
def Candidate.build (c : Candidate) (N : Network) (n r : ℕ) : Except Diagnostic Circuit
def select (budget : Grade) (p : Pref) (cs : List (α × Grade)) : Option (α × Grade)
theorem select_spec : the result is in cs, is admissible, and has no admissible element of cs
  strictly below it; it is none iff no element of cs is admissible
```

Details:
- **`lexLt`** is either a `Bool` function or the core list order with its `Decidable` instance.
  Confirm the name before using it (rule 2).
- **`Candidate.build`** is exactly the builder of (8′) for each constructor. A `#guard` test
  checks that it agrees with the circuit `groverInstance` builds at the candidate's shape and
  mode.
- **`select`** returns the first admissible element with the least key.
- **`select_spec`** is proved once, for any list. Choose the exact form.

`CQRV.lean` and `Apps/cqr/Main.lean` import the module.

### G2. The certificate (renderer next to `renderCert`)

`cqr certify --budget … --prefer …` writes the ordinary `Cert.lean` of the chosen candidate,
byte for byte as `cqr certify` writes it for that shape and mode. The selection block is
inserted before the final `end`:

```
/-! ## Certified selection (PHASE2_SPEC §A.6 (8), (8′)) — generated by `cqr certify --budget w,d,t,a --prefer p` -/
def budget : Grade := ⟨w, d, t, a⟩
theorem cand_grade_treeMbu : (Candidate.treeMbu.build net n r).map Synthesis.grade = .ok ⟨…⟩
theorem cand_grade_treeCoherent : …
theorem cand_grade_fewLogMbu : …
theorem chosen_fits : Synthesis.grade emitted ≤ budget
theorem selected : ∀ c ∈ candidates, ∀ C, c.build net n r = .ok C → Synthesis.grade C ≤ budget →
    ¬ lexLt (Grade.key p (Synthesis.grade C)) (Grade.key p (Synthesis.grade emitted))
#print axioms chosen_fits
#print axioms selected
```

- **The header stays as it is.** So removing the block gives back the ordinary file exactly.
- **The candidate grades.** For the chosen candidate, `cand_grade` follows from `emitted_ok` and
  `grade_eq`, with no second evaluation. For the other two, use `decide +kernel` through
  `except_ok_of_check` or an analogue for `Except.map`. If a builder fails at the instance, state
  the failure instead (for example `(c.build net n r).toBool = false`); the candidate is then
  not admissible.
- **`selected`** follows from the `cand_grade` theorems, `grade_eq` and `decide`.
- **The audit.** One kernel run audits `cert`, `chosen_fits` and `selected`.

### G3. The CLI (`Apps/cqr/Main.lean`)

```
cqr certify <file> --budget w,d,t,a --prefer width|depth|t|anc [--solutions M] [--iterations r]
            [--count-limit k] [--profile name|path] [--bench k] [--report] [--out dir]
```

**Refusals.** These get the usage message, exit 2, and write nothing:
- `--budget` without `--prefer`, or `--prefer` without `--budget`;
- a budget that is not four naturals;
- a `--prefer` value other than the four;
- `--budget` together with `--shape`, `--uncompute` or `--problem count`.

**The run.**
1. The front end, the signature, and Algorithm 2. A non-match prints the proved hint.
2. The three candidates through `groverInstance` at their (shape, mode), with their grades.
3. `select`.
   - **No candidate fits:** a diagnostic with stage `synthesis` and the new code
     `budget_unsatisfiable`, whose message lists every candidate's grade. Exit 1; nothing is
     written.
   - **Otherwise:** the ordinary certificate path of `cqr certify` for the chosen candidate,
     including `--profile`, `--bench` and `--report`, plus the selection block. The JSON is
     1.11.0 with `selection`. The status line is the ordinary one. One extra line follows it:
     `selection: <shape> + <mode> (prefer <p>; budget (w, d, t, a); k of 3 candidates
     admissible)`.

**The output.** The default directory is `certs/<name>_sel`. With `--report`, the run report
lists the candidates, their grades, their admissibility, and the choice.

**The ordinary path.** A run without `--budget` takes exactly the old code path, and its output
stays byte-identical.

### G4. Schema 1.11.0 (`docs/certificate.schema.json`, `tests/diff/cert_schema.py`)

- **`selection`** is required under 1.11.0 and allowed only there, and only for pattern Grover.
  Otherwise 1.11.0 requires what 1.10.0 requires for Grover (`grade_kind "measured"`, and the
  rest).
- **The shape of `selection`:**
  - `budget`: {w, d, t, a}, naturals;
  - `prefer`: one of width, depth, t, anc;
  - `order`: four distinct letters;
  - `candidates`: exactly 3 objects with `shape` (tree / few:log), `uncompute` (mbu / coherent),
    `grade` (an object or null) and `admissible` (a boolean);
  - `selected`: {shape, uncompute};
  - `theorem`: a string.
- **The top-level description** gains v1.11.0.
- **Envelopes of 1.10.0 and earlier** stay valid under their own versions.

`cert_schema.py`:
- every committed certificate validates, the new selection directory included;
- new negatives:
  - `selection` under 1.10.0;
  - 1.11.0 without `selection`;
  - `selection` on a Count envelope;
  - `prefer` outside the enum;
  - two candidates instead of three;
  - a budget with a missing or negative component.

The semantic rules that a schema cannot express are checked in G5:
- `order` starts with the preferred letter;
- `admissible` equals grade ≤ budget;
- `selected` is the least admissible candidate.

### G5. Checks and tests

**`tests/diff/select_check.py`** (new). It runs from `scripts/check_select.sh`, the new CI step
"Certified selection (Stage 21a4)", added to `.github/workflows/ci.yml` and
`scripts/ci_local.sh`; update the pass-mark comment to 19. The step does the following:
- **The committed directory** `examples/certs/grover_pred_037_sel` (new) is regenerated by
  `cqr certify examples/grover_pred_037.cqr --budget 12,200,100,8 --prefer depth --report --out
  <tmp>`. Checks:
  - the run is certified;
  - `Cert.lean`, `.qir` and `.qasm` are byte-identical to the committed directory, and the JSON
    is equal outside `reference_configuration`;
  - the selected candidate is `fewLogMbu`: depth alone would pick `treeMbu`, but its w = 15
    exceeds 12;
  - the three candidate grades equal the `grade` of the committed `grover_pred_037`,
    `grover_pred_037_coh` and `grover_pred_037_few` certificates;
  - `.qir` and `.qasm` are byte-identical to those of `grover_pred_037_few`;
  - `Cert.lean` with the selection block removed is byte-identical to
    `grover_pred_037_few/Cert.lean`.
- **A second run**, `--budget 20,300,200,8 --prefer depth`, into a temporary directory:
  certified, `treeMbu` selected, `.qir` and `.qasm` byte-identical to `grover_pred_037`'s.
- **For both runs**, the semantic rules of G4: `admissible`, `order`, and the choice against
  Python's own argmin, with ties broken by list order.
- **No fit**, `--budget 9,300,300,9 --prefer depth`: exit 1, code `budget_unsatisfiable`, the
  three grades in the message, nothing written.
- **The refusals of G3:** exit 2, nothing written.
- **Two negative kernel tests**, through `CertifyTool audit` on mutated copies of the committed
  `Cert.lean`:
  - (h1) `budget` raised to ⟨15, 200, 100, 8⟩. `chosen_fits` still holds, but `selected` fails,
    because `treeMbu` is now admissible with d = 134 < 172.
  - (h2) the grade in `cand_grade_treeCoherent` lowered by one. The kernel check fails.

**`scripts/print_axioms.sh`** audits `cert`, `chosen_fits` and `selected` of the committed
selection directory.

**Lean tests** (`tests/CQRVTests/Select.lean`, new; Physlib-free):
- `Grade.key` for each preference;
- `select` on the three `grover_pred_037` grades under a generous budget: depth → `treeMbu`,
  width → `fewLogMbu`, t → `treeMbu`, anc → `fewLogMbu`;
- budget ⟨12, 200, 100, 8⟩ with depth → `fewLogMbu`; a budget that fits nothing → `none`;
  equal grades → the first in the list;
- `#guard_msgs` on `#print axioms select_spec`;
- `Candidate.build` against `groverInstance` on a four-input program, for each candidate.

### 21a4 Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry;
- `docs/PROJECT_STATUS.md`;
- README: the status line (Stage 21a complete), one sentence on `--budget` / `--prefer`, and the
  usage text.

Acceptance:
- `lake build` green;
- CI 19 PASS, 0 FAIL, 4 n/a;
- the invariants hold;
- the axioms of `select_spec`, `chosen_fits` and `selected` are the standard three (or a subset);
- every new negative test is rejected.

Report:
- the kernel time of the selection certificate;
- the time of the new step;
- the times of steps 7 and 22.

Stop and ask in any of these cases:
- a byte of a committed `Cert.lean`, `.qir` or `.qasm` changes, or a committed directory would
  need regenerating;
- `selected` cannot be stated over the builders as in (8′); report it and propose a form;
- a statement of mine is false; give the counterexample and the corrected form;
- a Lean process above 8 GB, or a kernel check above 10 minutes;
- the new step above 600 s, or step 22 more than 60 s slower than 701 s; report the times and do
  not trim checks.

## 21m — The M3 close: the header fix and the M3 report (written at the M3 review, 2026-11-15)

PHASE2_SPEC §A.9, items (6) and (7). Precondition: main = the M3 review commit. Start with
`git switch -c stage-21m main`. The reviewer's edits for this task are committed with the M3
review.

**Invariants of 21m.**
- **One committed proof file changes, in one line.** That file is the counting certificate
  `examples/certs/grover_pred_037_count/Cert.lean`, and the line is its header (H1). Its `.qir`
  and `.qasm` stay byte-identical. The four Grover directories and `grover_pred_037_sel` are not
  regenerated and not edited.
- **No theorem statement changes.** The only Lean change is the header line of `renderCountCert`
  and its doc-comment. So the search outputs are not affected; the 126-run comparison is not
  needed.
- **No new CI step.** The pass mark stays **19 PASS, 0 FAIL, 4 n/a**.
- **`docs/M2_REPORT.md` stays frozen.**
- **`docs/paper/` is neither read nor edited** for the M3 report.

### H1. The header fix (`CQRV/Certify/CountCert.lean`)

Change the header line of `renderCountCert` to:

```
# Certificate `{name}_count` (generated by `cqr certify --problem count`; do not edit)
```

Remove from its doc-comment the sentence about keeping the old line for byte identity. Then
regenerate the counting certificate with the 21a3 command:

```
cqr certify examples/grover_pred_037.cqr --problem count --precision 4 --report \
  --out examples/certs/grover_pred_037_count
```

Check the result field by field against a copy taken before:
- `Cert.lean` differs in exactly the header line;
- `.qir` and `.qasm` are byte-identical;
- `certificate.json` changes only in `proof_hash` and the machine fields of
  `reference_configuration`;
- `run_report.{md,json}` change only in their timing and machine lines, and in any line that
  quotes the proof hash.

Update any check in `tests/diff/certify_check.py` that names the old header text.

### H2. `docs/M3_REPORT.md` (new)

It is the input for report v5 and for the Stage 30 revision of Paper 1, in the manner of
`docs/M2_REPORT.md`.

**Rules for every number:**
- It is measured by this repository, and it names its source: a committed JSON, the log of the
  acceptance CI run (`.lake/ci_local/`), the output of `scripts/print_axioms.sh`, or a command
  given in the report.
- A number that cannot be measured is written as "not measured", never estimated.
- A figure of report v3 appears only in the errata table of §8, where it differs from the
  measured one.

Sections:
1. **What is certified.**
   - The theorem table: name, report or PHASE2_SPEC section, and axioms. It lists every theorem
     that `print_axioms.sh` audits, plus the Stage 14–21 library theorems that carry a claim:
     the QFT, the counting circuit, `ae_parametric_lemma` / `ae_parametric_lemma_mk`,
     `matchLibrary_spec`, `groverSem`, `countSem`, `select_spec`.
   - The six committed certificates: each one's theorem in one or two lines, `grade` and
     `grade_kind`, ε and δ, the kernel time, and the gate counts.
2. **The pipeline end to end, per pattern.** The command, and each stage with its status (proved,
   kernel-checked or unverified). Then the trust boundary: what is unverified, and what binds it
   (`predicate_hash`, the front-end theorem).
3. **Proposition 5.1.** What is proved, and for which fragment. Uniform arity is necessary; give
   the counterexample. The cost bound is not formalized.
4. **Certified selection.** The candidate space, the order, and what `selected` states. Then what
   selection cannot see: `treeCoherent` is dominated, and its advantage lies in `grade_ext`.
5. **Measured numbers.**
   - the CI table of the acceptance run of this task (each step and its time);
   - the kernel times of the six certificates;
   - the size of the `cqr` closure;
   - `wc -l` of the modules added in Stages 18–21.
6. **Deviations and open items.**
   - The deviations recorded in `docs/DECISIONS.md` for Stages 14–21 that bear on a claim: one
     line each, with the date.
   - The open items, each with the destination decided in §A.9.
7. **Claims for Paper 1.**
   - A table of claim, evidence (theorem, file, CI step) and exact scope.
   - Then the claims not to make: "verified on hardware"; matcher completeness beyond the
     implemented fragment; optimality beyond the stated candidate space; a formal cost bound for
     matching; any claim for M = 0 in counting; any claim that a hardware run validates a
     certificate.
8. **Errata against report v3.** Every figure of report v3 that the M3 report states and that
   differs from the measured value, with both values.

Keep the report under 300 lines.

### H3. Docs

- a DECISIONS.md entry;
- `docs/PROJECT_STATUS.md`;
- README: the status line ("M3 reached; Stage 21a complete") and a link to `docs/M3_REPORT.md`.

### 21m Acceptance / Stop

Acceptance:
- `lake build` green;
- CI 19 PASS, 0 FAIL, 4 n/a;
- the invariants hold (give the changed fields of the counting directory);
- every number in the M3 report names its source.

Stop and ask in any of these cases:
- anything other than the header line changes in the counting `Cert.lean`, or another committed
  directory changes;
- a number would have to be estimated;
- writing a section would need `docs/paper/`;
- a Lean process above 8 GB, or a kernel check above 10 minutes.

## 21b1 — The feasibility probe for measured composition (written at the 21m review, 2026-11-15)

PHASE2_SPEC §A.7, §A.9 (1), and the refinement at the 21m review. Precondition: main = the 21m
review commit. Start with `git switch -c stage-21b1 main`.

**What the probe is.** It answers Q1–Q5 below and recommends the route of 21b2. It writes no
certificate, adds nothing to `CQRV/`, and changes no committed certificate. Its outputs:
- `docs/notes/PROBE_21B1.md` (new): the answers, the tables, and the recommendation;
- `scripts/probes/probe_21b1.py` (new): the numeric table, run with
  `.venv/Scripts/python.exe -I`;
- `scripts/probes/Probe21b1.lean` (new): a standalone file, checked with
  `lake env lean scripts/probes/Probe21b1.lean`. It is outside the build and CI, and holds the
  statements and proof attempts of Q1, Q2 and Q4.

**The statement route (a) aims at.** It composes two stages:
- **Stage 1** is the counting channel `groverChannel (n+m) C₁` at precision m, decoded by
  `countPOVM n m a`. It realizes `CountSpec m a` with (`ae_eps a m`, `ae_delta`); this is the
  `cert` of a counting certificate.
- **Stage 2** is a channel Ψ on `CountOut m a`. On input y it runs Grover with r(y) iterations,
  where:
  - r(y) := `rStar n (M̃ y)`;
  - M̃ y := the nearest integer to 2^n · `countEst m a y`, clamped to [1, 2^n].

  Its output is the search register, and its declared grade is the maximum of the Grover
  circuits' grades over all y.
- **The search specification** is restricted to the good estimates: `S_g y z :=
  |countEst m a y − a| ≤ ae_eps a m ∧ P z`, with output `DiscreteOut (Reg n)` and decoding
  `basisPOVM n`.

Composed by Theorem 3.3a, this gives
`Realizes (S_g.comp (CountSpec m a)) (basisPOVM n) (measuredComp Φ₁ (countPOVM n m a) Ψ)
(ae_eps a m) (ae_delta + δ_g) (g₁ + g₂)`, where δ_g is the maximum of `groverDelta (r y) n M`
over the y in the domain of `S_g`.

**Q1 — Theorem 3.3a on a pseudo-metric.**
- In the probe file, state `measured_composition` with `[PseudoMetricSpace Y]` and
  `[PseudoMetricSpace Z]`, and prove it, reusing the existing proof where possible.
- If a lemma it uses (`relax_comp`, `mixture_union_bound`, the relaxation) needs a metric, name
  it.

**Q2 — Stage 2 as a `GradedChannel`.**
- Find the Physlib construction for a measure-and-prepare channel: measure the input in the
  computational basis, then prepare a state σ_y. Name it (rule 2), or build Ψ from existing
  pieces, such as `POVM.measureDiscard` followed by a classical-to-quantum map.
- In the probe file, prove `Ψ.chan (encode y) = (groverChannel n (C (r y))).chan (encode ())`.
  Here C r is the Grover circuit at r iterations: a family of circuits with their `= .ok` proofs
  from `groverCircuit N n r`.
- If nothing exists and building it would take more than about 300 lines, stop at the statement
  and give the size.

**Q3 — The numbers.** `probe_21b1.py` computes, for (n, M) = (8, 32) (`grover_pred_037`) and
(6, 30) (`simple_alu_x0_1`), and for m = 4, 5, 6, 7:
- ε_f = `ae_eps a m`;
- the domain D: the outcomes y ∈ 0 … 2^m − 1 with |`countEst` − a| ≤ ε_f;
- r(y) for y ∈ D, with `rStar` exactly as `CQRV.Synthesis.rStar` computes it (the Float
  formula);
- δ_g: the maximum of `groverDelta` (exact rational) over D and the ideal point;
- the composite δ = `ae_delta` + δ_g, and whether it is below 1;
- the margins: the least |est − a| − ε_f over y ∉ D, and the least ε_f − |est − a| over y ∈ D
  (the precision a Lean proof of membership needs);
- the composed grade of stage 1 at that m (from a `cqr certify --problem count` JSON, or from the
  `counting-sample` of CertifyTool), and the grade of stage 2 (the maximum over y).

The reviewer's arithmetic in the refinement is a guess to check, not a fact.

**Q4 — The Lean cost of the domain.**
- For the candidate instance, the δ_g bound needs a proof that y ∉ D for every y whose r(y) is not
  the good r. Each is a strict real inequality between |sin²(π y/2^m) − a| and `ae_eps a m`.
- Confirm by `#check` the Mathlib bounds on π and on sin (Taylor bounds).
- In the probe file, prove the tightest exclusion inequality of the candidate instance. Give its
  size and check time, and the number of such inequalities (y ↔ 2^m − y is a symmetry).

**Q5 — Stage 1 at the candidate m.** Run `cqr certify examples/grover_pred_037.cqr --problem
count --precision m --out <tmp>` once for the candidate m, without committing. Report the kernel
time, the peak memory and the composed grade.

**The recommendation for 21b2.** Either:
- route (a) at a stated instance, with a size estimate and the list of new library pieces
  (`measured_composition_pseudo`, the measure-and-prepare channel, the domain lemmas, the
  composite theorem, a committed certificate or not); or
- route (b), with the reasons.

### 21b1 Docs / Acceptance / Stop

Docs: a DECISIONS.md entry and `docs/PROJECT_STATUS.md`. README is unchanged.

Acceptance:
- Q1–Q5 answered, each with evidence (the probe file's check output, the script's table, the
  certify run);
- the recommendation;
- `lake build` green and unchanged.

No CI run is required: nothing CI checks changes. The commit holds only the three probe files and
the two docs.

Stop and ask in any of these cases:
- a Lean process above 8 GB, or a kernel check above 10 minutes;
- the probe would need a change to `CQRV/` or to a committed certificate;
- a statement of mine is false; give the counterexample and the corrected form.

## 21b2 — Search with an unknown number of solutions: Theorem 3.3a exercised (written at the 21b1 review, 2026-11-15)

PHASE2_SPEC §A.7, §A.9 (1), the "21b1 done" paragraph and the refinements (9)–(12).
`docs/notes/PROBE_21B1.md` and `scripts/probes/Probe21b1.lean` are the starting point.
Precondition: main = the 21b1 review commit. Start with `git switch -c stage-21b2 main`.

**Invariants of 21b2.**
- **No existing theorem statement changes.** `measured_composition` stays as it is; the pseudo
  form is a new theorem.
- **Nothing is regenerated.** No certificate changes, and the search outputs are untouched: no
  CLI change.
- **The `cqr` closure is unchanged.** The new modules are Physlib-side and imported by
  `CQRV.lean` only.
- **No new CI step.** The pass mark stays 19 PASS, 0 FAIL, 4 n/a.

### J1. Library pieces

- **`measured_composition_pseudo`** goes in `CQRV/Realizability/Composition.lean`: Theorem 3.3a
  with `[PseudoMetricSpace Y] [PseudoMetricSpace Z]`, with the proof of the probe.
- **`CQRV/Realizability/MeasurePrepare.lean`** (new) holds the measure-and-prepare channel of
  the probe: `mpChoi`, `mpChoi_psd`, `mpChoi_traceLeft`, `measurePrepare`,
  `measurePrepare_encode`. Add a doc-comment saying what it is: the channel
  ρ ↦ ∑_y ⟨y|ρ|y⟩ σ_y, of which the encoded basis states are the case the composition needs.

### J2. `CQRV/Grover/SearchUnknownM.lean` (new, Physlib-side)

- **`searchStage (C : CountOut m a → Circuit) (g : Grade)`** is the stage-2 `GradedChannel`:
  `measurePrepare` of `y ↦ (groverChannel n (C y)).chan (encode ())`, with declared grade `g`.
  `searchStage_encode` states its value on `encode y`.
- **`SearchAfterCount m a P ε : Spec (CountOut m a) (DiscreteOut (Reg n))`** is
  `fun y z => |countEst m a y − a| ≤ ε ∧ P z`. Lemmas:
  - its domain, under `1 ≤ M`: the y with |countEst − a| ≤ ε;
  - non-expansiveness (take z = z');
  - domain compatibility with `CountSpec m a` at ε (`countSpec_relax`).
- **`searchStage_realizes`.** Realizes `SearchAfterCount` with ε = 0 and
  δ = 1 − sin²((2r₀+1)θ). Its hypotheses:
  - the good-domain hypothesis: every y in the domain has `C y = C₀`;
  - C₀ = the Grover circuit at r₀;
  - the branch facts that `groverSem` needs.

  The proof is `groverSem.proof` per branch, through `searchStage_encode`.
- **`search_unknown_M`, the composite.** For the parameters of `countSem` (stage 1, circuit C₁)
  and of `groverSem` (stage 2, circuit C₀ at r₀), a circuit family C with the good-domain
  hypothesis, and a grade g₂ with `∀ y, Synthesis.grade (C y) ≤ g₂` (refinement (9)):
  `Realizes ((SearchAfterCount m a P (ae_eps a m)).comp (CountSpec m a)) (basisPOVM n)
  (measuredComp (groverChannel (n+m) C₁) (countPOVM n m a) (searchStage C g₂)) (ae_eps a m)
  (ae_delta + (1 − sin²((2r₀+1)θ))) (Synthesis.grade C₁ + g₂)`.
  - Proof: `measured_composition_pseudo` applied to `countSem.proof` and
    `searchStage_realizes`, with the two free hypotheses.
  - Choose the exact parameter form, keeping to refinements (10) and (11).
  - State the corollary with δ as a rational through `groverDelta`, as the certificates'
    `delta_eq` do.
- **`domain_8_32_5`, the domain lemma at the instance.** Every y : CountOut 5 (32/2^8) with
  |countEst − 1/8| ≤ `ae_eps (1/8) 5` is the ideal point or one of the outcomes 3, 4, 28, 29
  (state the outcomes as `Reg 5` values in a form `decide` can use).
  - Use the monotonicity of sin² on [0, π/2] and the symmetry y ↔ 32 − y, so that only the two
    boundary inequalities (y = 2 and y = 5) need real bounds.
  - Use the confirmed π bounds `Real.pi_gt_d4` / `Real.pi_lt_d4` (or d6) and `Real.sin_le` /
    `Real.sin_gt_sub_cube` (confirm each name).
- **`search_unknown_M_8_32_5`, the corollary at the instance.** n = 8, M = 32, m = 5, r₀ = 2,
  δ = 1 − 8/π² + 7/128. Its remaining hypotheses are only:
  - the circuit equalities (`countingCircuit … = .ok C₁`, `groverCircuit … 2 = .ok C₀`);
  - the network facts;
  - the table property `∀ y ∈ {3, 4, 28, 29}, C (inl y) = C₀`, and `C (inr ()) = C₀`;
  - the grade bound.

  All of these are decidable at the instance.

### J3. Tests and the numbers

**`tests/CQRVTests/SearchUnknownM.lean`** (new):
- `#guard_msgs` on the axioms of `measured_composition_pseudo`, `measurePrepare_encode`,
  `search_unknown_M`, `domain_8_32_5` and `search_unknown_M_8_32_5`;
- an `example` that applies the corollary with its hypotheses as hypotheses (as the `countSem`
  test does).

**`scripts/probes/probe_21b1.py`** prints, in addition, for (8, 32, 5):
- the full table y ↦ r(y);
- the largest r and the Grover grade there, which is the honest g₂ of refinement (9), by
  `CertifyTool` or a `cqr synthesize` at that r;
- the composite grade `(21, 2862, 1364, 8) + g₂`.

Put these numbers in `docs/notes/PROBE_21B1.md` under a heading "21b2", and in the doc-comment of
`search_unknown_M_8_32_5`. Change nothing else in the probe note.

### 21b2 Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry;
- `docs/PROJECT_STATUS.md`;
- one line in README's status;
- in `docs/M3_REPORT.md` §7, the row on Theorems 3.3a / 3.3b: replace "3.3a is not yet exercised
  on two certified stages (21b)" with the exact form of (12). Nothing else in the report changes.

Acceptance:
- `lake build` green;
- CI 19 PASS, 0 FAIL, 4 n/a;
- the axioms of J3 are the standard three;
- the honest g₂ and the composite grade are stated.

Stop and ask in any of these cases:
- `measurePrepare` needs more than about 150 lines in library form, or `domain_8_32_5` more than
  about 300;
- a statement of mine is false (give the counterexample and the corrected form);
- a Lean process above 8 GB, or a kernel check above 10 minutes;
- the composite cannot be stated over the two QPLP records; report it and propose the direct
  form.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests, (d) SORRIES.md, (e) open questions.
- (c) gives the CI summary and, for 21a1, the number of byte-compared search runs; for 21a2, the
  axiom line of `matchLibrary_spec` and the line count of the proofs; for 21a4, the kernel
  time of the selection certificate and the times of the new step and of steps 7 and 22.
- (e) says what the next task should know.
