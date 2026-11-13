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
- **21a3**, the QPLP record and `cqr certify --problem count`, gets its detailed text at the 21a2
  review (the outline below fixes its scope);
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

## 21a3 — The QPLP record and `cqr certify --problem count` (outline; detailed at the 21a2 review)

Scope, fixed by §A.5 amendments (5)–(7):

1. **The record.** `CQRV/Patterns/Basic.lean` (Physlib-free) gets the syntactic QPLP record:
   - its fields: the entry, the specification name, the lemma name, the grade kind and the builder
     dispatch;
   - `qplpLibrary`, with `qplpLibrary.map (·.entry) = library`;
   - `groverInstance` becomes a dispatch on the matched entry.

   `CQRV/Patterns/Sound.lean` (Physlib-side) gets `QPLP.Sem`, the dependent record of
   Definition 4.1 with its proof field, instantiated for Grover from
   `grover_parametric_lemma_gen` and for Count from `ae_parametric_lemma_mk`.
2. **The command.** `cqr certify --problem count --precision m` goes through the dispatch to
   `CountCert`. It takes `[--count-limit k] [--uncompute mbu|coherent] [--bench k] [--report]
   [--out dir]`.
   - **Refused** (usage, exit 2): `--solutions`, `--iterations`, `--profile`, and `--shape` other
     than tree.
   - **M = 0 with n ≤ limit**: refused before anything is written (diagnostic, exit 1).
   - **n > limit**: the certificate has `cert` only, `solution_count` is `{null, "not_decided"}`,
     and the status line ends "solution count not decided".
3. **Version 1.10.0 everywhere.**
   - The four Grover certificates are regenerated at 1.10.0 with `grade_kind "measured"`; only
     their `certificate.json` changes.
   - The schema's top-level `grade` description is reworded.
   - `CertifyTool count-certify` is removed. `cqr certify --problem count` writes
     `examples/certs/grover_pred_037_count`, with `Cert.lean`, `.qir` and `.qasm` byte-identical.
   - The checks move into `certify_check.py`.

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
