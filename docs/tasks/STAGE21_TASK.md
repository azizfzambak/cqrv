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
- **21a4**, certified selection, gets its detailed text at the 21a3 review (outline below).

**21b**, the stretch of §A.7, is unchanged and is decided at the M3 review.

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

## 21a4 — Certified selection (outline; detailed at the 21a3 review)

The scope is fixed by §A.6 amendment (8):
- **Requests.** Search requests only.
- **Flags.** `--budget w,d,t,a` and `--prefer depth|width|t|anc`.
- **Candidates.** The three certified pairs (tree, mbu), (tree, coherent), (few:log, mbu) at the
  request's r.
- **What the certificate states.** Every candidate's grade (`decide +kernel`) and `selected`: the
  chosen candidate fits the budget, and no admissible candidate is smaller in the lexicographic
  order that starts with the preferred component.
- **CI.** A new CI step. The pass mark becomes 19.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests, (d) SORRIES.md, (e) open questions.
- (c) gives the CI summary and, for 21a1, the number of byte-compared search runs; for 21a2, the
  axiom line of `matchLibrary_spec` and the line count of the proofs.
- (e) says what the next task should know.
