# M3 report — two certified patterns, Proposition 5.1, certified selection (Stage 21m, 2026-11-15)

Input for report v5 and for the Stage 30 revision of Paper 1, in the manner of `docs/M2_REPORT.md`
(frozen). Milestone M3 (PHASE2_SPEC §A.9): Grover and Count certified end to end, Proposition 5.1
proved for the implemented fragment, selection under a budget certified. Every number below is
measured by this repository and names its source: a committed `certificate.json`, the acceptance CI
log (`.lake/ci_local/`), the output of `scripts/print_axioms.sh`, or a command given here. "Not
measured" is written where nothing was measured. Figures of report v3 appear only in §8.

Toolchain (the `reference_configuration` of every committed `certificate.json`): Lean
`leanprover/lean4:v4.35.0`, Mathlib at the `v4.35.0` tag, Physlib `96a6bc5e…`; machine: the `cpu`
field (13th Gen Intel Core i9-13900H, 20 logical CPUs, Windows 11), `LEAN_NUM_THREADS=4`.

## 1. What is certified

### 1.1 Theorems and their axioms

Source: `scripts/print_axioms.sh` as CI step 8 "Axiom audit (blocking)" of the acceptance run of
21m (`.lake/ci_local/`, 213 s), and `#print axioms` on the library theorems (the `#guard_msgs` of
`tests/CQRVTests/*.lean` pin the ones marked †). "Standard" means exactly `propext`,
`Classical.choice`, `Quot.sound`.

| Theorem | Section | Axioms |
|---|---|---|
| `CQRV.Certify.grover_certificate`, `grover_certificate_few`, `grover_certificate_few_all`, `grover_certificate_coherent` (the certificate lemmas) | report §5.1.3, §8.4.1; PHASE2_SPEC §A.0.1 | standard |
| `CQRV.Certify.sin_sq_odd_mul`, `sin_mul_chebyshevU`, `chebyshevU_go_even`, `chebyshevU_go_succ` (exact δ) | §8.2 | standard |
| `CQRV.Synthesis.Network.countSat_eq_card`, `bitsEquiv_apply` (the kernel-decided count) | §8.2 (Stage 14a) | standard |
| `CQRV.Certify.except_eq_ok_okPayload` | §8.4.1 | `propext` |
| `CQRV.Certify.except_ok_of_check` | §8.4.1 | none |
| `CQRV.Grover.grover_parametric_lemma`, `_gen`, `_diff` | §8.2–8.3, Fig. 8.1; §A.0.1 | standard |
| `CQRV.lemma_6_3_2_xor`, `lemma_6_3_2_coherent` (Lemma 6.3.2, both modes) | §6.3.2; §A.0.1 | standard |
| `CQRV.Synthesis.toNetwork_pred` (the front end) | §4; Stage 16a | standard |
| `CQRV.measured_composition`, `coherent_composition` (Theorems 3.3a, 3.3b) | §2.3.2 | standard |
| `CQRV.qft_basis`, `aqft_diamond_le`, `aqft_adjoint_diamond_le` (QFT, AQFT bounds) | §A.2 (Stage 18) | standard |
| `CQRV.Synthesis.grade_assembleCounting_le` (⊕ as a bound) | §3.1.4; §A.3 (Stage 19a) | standard |
| `CQRV.Counting.countingCircuit_ancRestore` (the counting circuit restores) | §A.3 (Stage 19c) | standard |
| `CQRV.Grover.phaseDist_eq`, `qpe_success` (the QPE bound) | §A.4 (Stage 20a) | standard |
| `CQRV.Grover.ae_parametric_lemma`, `ae_parametric_lemma_mk`, `ae_parametric_lemma_aqft` | §A.4 (Stage 20b) | standard |
| `CQRV.Matching.millerMatch_sound`† | §4.1.2 | standard |
| `CQRV.Matching.millerMatch_complete`, `matchLibrary_spec`† (Proposition 5.1) | §4.2.1; §A.5 (4) | standard |
| `CQRV.Patterns.groverSem`†, `countSem`† (Definition 4.1 instances) | §3.2; §A.5 (6′) | standard |
| `CQRV.Patterns.select_spec`† (certified selection) | §A.6 (8′) | standard |
| `CQRV.Cert.grover_pred_037.cert`, `.front_end` (four directories: `grover_pred_037`, `_few`, `_coh`, `_sel`); `CQRV.Cert.simple_alu_x0_1.cert`, `.front_end`; `CQRV.Cert.grover_pred_037_count.cert`, `.cert_count`, `.front_end`; `CQRV.Cert.grover_pred_037.chosen_fits` (`propext`, `Quot.sound`), `.selected` | §8.4.4; §A.4, §A.6 | standard (as noted) |

### 1.2 The six committed certificates (`examples/certs/`, each `certificate.json`)

Each Grover `cert`: `RealizesExact (SearchSpec (Network.pred net n)) (basisPOVM n) (groverChannel n
emitted) δ g ∧ AncRestore n a emitted (groverOp (Network.pred net n) ^ r * hadamardU n)`, with no
hypothesis (`hM_count` decides M). The counting `cert`: `∀ M, card = M → 1 ≤ M → Realizes (CountSpec
m (M/2^n)) (countPOVM n m (M/2^n)) (groverChannel (n+m) emitted) (ae_eps (M/2^n) m) ae_delta g ∧
AncRestore (n+m) emitted.nAnc emitted (U_count (Network.pred net n) m none)`; `cert_count` is its
instance at M = 32. The selection certificate adds `chosen_fits : grade emitted ≤ budget` and
`selected` (§4).

| Directory | Pattern; instance | `grade` (w, d, t, a); `grade_kind` | `grade_ext` (2Q, T-depth, rot, meas, ff) | ε; δ | Kernel (s) | G (unitary, meas, ff, terminal) |
|---|---|---|---|---|---|---|
| `grover_pred_037` | Grover; n = 8, M = 32, r = 2, tree + mbu | (15, 134, 72, 7); measured | (126, 39, 0, 18, 36) | 0; 7/128 | 12.8 kernel, 23.7 wall (median of 5) | 390 (328, 18, 36, 8) |
| `simple_alu_x0_1` | Grover; n = 6, M = 30, r = 1 | (16, 121, 60, 10); measured | (137, 28, 0, 15, 30) | 0; 833/2048 | 13.0, 23.9 (median of 5) | 345 (294, 15, 30, 6) |
| `grover_pred_037_few` | Grover; few:log + mbu | (10, 172, 96, 2); measured | (106, 77, 0, 8, 16) | 0; 7/128 | 11.2, 22.1 (median of 5) | 380 (348, 8, 16, 8) |
| `grover_pred_037_coh` | Grover; tree + coherent | (15, 200, 144, 7); measured | (216, 74, 0, 0, 0) | 0; 7/128 | 23.3, 34.2 (median of 5) | 552 (544, 0, 0, 8) |
| `grover_pred_037_count` | Count; n = 8, m = 4, M = 32 (kernel-decided), exact inverse QFT, mbu | (20, 1388, 660, 8); composed_bound | (1161, ≤ 660, 6, 165, 330) | 2π√(a(1−a))/2⁴ + π²/4⁴ ≈ 0.168426 at a = 32/256; 1 − 8/π² ≈ 0.189431 | 18.6, 29.8 (single run) | 3364 (2857, 165, 330, 12) |
| `grover_pred_037_sel` | Grover; `--budget 12,200,100,8 --prefer depth` → few:log + mbu | (10, 172, 96, 2); measured | (106, 77, 0, 8, 16) | 0; 7/128 | 25.4, 36.3 (single run) | 380 (348, 8, 16, 8) |

The kernel times are the `kernel_check` fields; the Grover ones are the medians of `--bench 5` at
the Stage 21a3 regeneration (2026-11-13), the counting one the 21m regeneration, the selection one
the 21a4 generation. Hashes: the `hashes` field of each JSON. The run reports (`run_report.{md,json}`)
give every stage's measured resources.

## 2. The pipeline end to end, per pattern

**Search** — `lake exe cqr certify <file> [--solutions M] [--iterations r] [--count-limit k]
[--shape tree|few:log] [--uncompute mbu|coherent] [--profile p] [--bench k] [--report] [--out dir]`.
**Count** — `… --problem count --precision m [--count-limit k] [--uncompute mbu|coherent] [--bench k]
[--report] [--out dir]`. **Selection** — `… --budget w,d,t,a --prefer width|depth|t|anc` (search
requests only). The stages (the rows of every `run_report.md`):

| Stage | Search (Grover) | Count | Status |
|---|---|---|---|
| 1a parser, surface checker, typed-term printer | `parse`, `check`, `renderLean` | same | unverified; declared trust boundary; `predicate_hash` binds the source |
| 1b typed AST → network | `toNetwork_pred`; `prog`, `prog_scoped`, `net_ok`, `front_end` in `Cert.lean` | same | proved; kernel-checked at the instance |
| 2 spec extraction ℰ | `SigmaIn` (n, M when a conjunction of literals, the oracle structure) | `withProblem (count m)` adds the class and `m` | unverified; the certificate restates n, M, `net` |
| 3 matching (Algorithm 2) | `groverEntry` | `countEntry` (F₆ : any, F₅ ≥ 1) | `millerMatch_sound`, `matchLibrary_spec` proved for the algorithm; the run itself is not kernel-checked |
| 4 QPLP instantiation | `instantiate` → `groverInstance`: `emitted_ok`, `grade_eq`, `gradeExt_eq`, `nAnc_eq`, `delta_eq` | `CountRequest.ofProgram`: six blocks, each `_ok`, `grade_eq`, `gradeExt_eq`, `liveEnd`; `emitted_ok` by `countingCircuit_of_blocks`; `grade_le` by `grade_assembleCounting_le` | kernel-checked |
| 5 oracle synthesis | `OracleCert` / `OracleCertCoh` (`synthesizeOracle net = .ok …`, `C.WF`) | controlled oracles inside every iterate block | kernel-checked; restoration by Lemma 6.3.2 |
| 6 ancilla restore | the `AncRestore` conjunct of `cert` | `countingCircuit_ancRestore` inside `ae_parametric_lemma` | proved |
| 7 certificate | `lake env lean Cert.lean`, `#print axioms` audited | `cert` and `cert_count` audited in one run | kernel-checked; axiom audit blocking |
| 8 QIR / OpenQASM 3 | `emitQIR`, `emitQASM` of `emitted` | same (`cp` decomposed in QIR) | unverified emitter; translation-validated by re-parse (CI steps 21–23) |

Outside the kernel: ℰ and the matcher (the theorem restates the instance), the emitter, the
Python harness, and the pinned Lean kernel and toolchain. Inside: everything `Cert.lean` states.

## 3. Proposition 5.1

`CQRV/Matching/Complete.lean` (Stage 21a2) proves, for the implemented algorithm on normal forms:
(i) `millerMatch_complete` — for φ in the fragment and a ground t, a well-formed matcher σ with φσ = t
makes `millerMatch φ t` succeed (its result extends into σ); `millerMatch_wf` — the result is well
formed; (i′) `matchers_agree` — two well-formed matchers agree on φ's metavariables (the match set is
empty or a singleton); `matchPrecondition_complete` with side conditions over φ's metavariables;
(ii) `library_match_unique` — no term matches two entries of `library`; (iii) `matchLibrary_noMatch`,
`matchLibrary_matched`, collected as `matchLibrary_spec`: a `matched e σ _` result names an entry
that t matches (σ a witness), no other entry matches, every well-formed matcher agrees with σ; a
non-`matched` result means no entry matches. `SigmaIn.toTerm_ground` shows every CLI term is ground.

**The fragment** is `MillerFragment φ := φ.isMillerPattern ∧ φ.uniformArity`: Miller patterns in
which every metavariable occurs with one argument count. Uniform arity is necessary: φ =
`c(λ. F x₀, λλ. F x₀ x₁)` and t = `c(λ. x₀, λλ. x₀)` are solved by `F ↦ λ. x₀` (since `subst` ignores
a binding's arity), but `millerMatch` builds `⟨1, x₀⟩` and `⟨2, x₀⟩` and fails with `inconsistent`
(the `#guard` of `tests/CQRVTests/Matching.lean`). Well-formed substitutions bind every metavariable
to a body without metavariables, closed below its arity and admitted by its sort. **The cost bound
(Proposition 5.1 (3)) is not formalized**: the implementation is one structural pass per entry with
early exit and no backtracking (documented in PHASE2_SPEC §A.5 (4)), not proved.

## 4. Certified selection

`CQRV/Patterns/Select.lean` (Stage 21a4; PHASE2_SPEC §A.6 (8), (8′)). The candidate space is the
three certified pairs, in this order: `treeMbu` (`groverCircuit N n r`), `treeCoherent`
(`… none .tree .coherent`), `fewLogMbu` (`groverCircuitFew N n r .logDepth`), at the request's r. A
candidate is admissible when its measured grade is ≤ the budget component-wise (report §3.1.2). The
order is lexicographic on the key (the preferred component, then the others in (w, d, t, a)); ties
go to the first in the list. `select_spec` (proved once, any list): the result is admissible and no
admissible element has a key strictly below it; `none` iff nothing is admissible.

A selection certificate states, for its instance, `cand_grade_c : Synthesis.grade <$> c.build net n r
= .ok g_c` for every candidate, `chosen_fits : Synthesis.grade emitted ≤ budget`, and
`selected : ∀ c ∈ candidates, ∀ C, c.build net n r = .ok C → Synthesis.grade C ≤ budget →
¬ lexLt (key p (grade C)) (key p (grade emitted))` — a claim about the builders' outputs, not about
a list of numbers, kernel-checked. **What selection cannot see:** for `grover_pred_037` at r = 2 the
grades are (15, 134, 72, 7), (15, 200, 144, 7), (10, 172, 96, 2); `treeCoherent` is dominated by
`treeMbu` component-wise, so no budget and no preference selects it. Its advantage is in
`grade_ext`: meas = ff = 0 against 18 and 36 (`grover_pred_037_coh` vs `grover_pred_037`), which the
(w, d, t, a) order does not see (destination: §6).

## 5. Measured numbers

### 5.1 The acceptance CI run of this task

The acceptance CI run of 21m (`scripts/ci_local.sh`, 2026-11-15, logs in `.lake/ci_local/`):
**19 PASS, 0 FAIL, 4 n/a**. Steps 1, 2, 9 and 20 have no local counterpart (checkout, elan,
setup-python, apt install of llvm; the QIR text is verified with llvmlite).

| Step | Name | Time (s) |
|---|---|---|
| 1–2 | checkout, elan | n/a |
| 3 | Fetch Mathlib cache | 198 |
| 4 | lake build | 3 |
| 5 | Warning check | 0 |
| 6 | Sorry check (+ self-test) | 43 |
| 7 | CLI smoke | 127 |
| 8 | Axiom audit (blocking) | 213 |
| 9 | setup-python | n/a |
| 10 | Python requirements + pip check | 1 |
| 11 | Simulator self-test | 0 |
| 12 | Differential oracle test | 28 |
| 13 | Front-end validation | 6 |
| 14 | Synthesized circuits = golden file | 2 |
| 15 | Diffusion and Grover circuit | 190 |
| 16 | Few-ancilla MCZ | 1 |
| 17 | QFT / AQFT | 8 |
| 18 | Counting circuit | 143 |
| 19 | Second worked predicate | 66 |
| 20 | Install llvm | n/a |
| 21 | SHA3, schema, QIR / QASM re-parse | 67 |
| 22 | cqr certify | 687 |
| 23 | Certified selection | 154 |

The previous run (the 21a4 acceptance, 2026-11-15; DECISIONS.md) was 19 PASS, 0 FAIL, 4 n/a with
step 23 in 154 s, step 22 in 688 s, step 7 in 126 s, step 8 in 216 s.

### 5.2 Kernel times

The `kernel_check` fields of §1.2: 12.8 / 13.0 / 11.2 / 23.3 s kernel for the four Grover
certificates (medians of 5), 18.6 s for the counting certificate and 25.4 s for the selection
certificate (single runs). In isolation on this tree: the counting section of
`tests/diff/certify_check.py` 213 s (two runs, the coherent and not-decided runs, two negative kernel
tests); `tests/diff/select_check.py` 168 s (Stage 21a4); `scripts/print_axioms.sh` 213 s (CI step 8).

### 5.3 The `cqr` closure

51 CQRV modules, external roots `Lean` and `Mathlib` only (no Physlib): the transitive `import`
closure of `Apps/cqr/Main.lean` over the repository's `.lean` files, counted with

```
python - <<'EOF'
import os, re
seen, q = set(), ["Apps.cqr.Main"]
while q:
    m = q.pop()
    if m in seen: continue
    seen.add(m); p = os.path.join(*m.split(".")) + ".lean"
    if os.path.exists(p):
        q += re.findall(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([\w.]+)", open(p, encoding="utf-8").read(), re.M)
print(len([m for m in seen if m.startswith("CQRV")]), sorted({m.split(".")[0] for m in seen if not os.path.exists(os.path.join(*m.split(".")) + ".lean")}))
EOF
```

### 5.4 Modules added in Stages 18–21

`git diff --name-status 9fc909b HEAD -- 'CQRV/*' | grep ^A | awk '{print $2}' | xargs wc -l` (9fc909b
is the Stage 17b commit):

| Module | Lines | Module | Lines |
|---|---|---|---|
| `CQRV/Circuit/CountingCorrect.lean` | 1440 | `CQRV/Grover/Counting.lean` | 434 |
| `CQRV/Matching/Complete.lean` | 1183 | `CQRV/Patterns/Select.lean` | 402 |
| `CQRV/Circuit/QFTCorrect.lean` | 797 | `CQRV/Circuit/Basis.lean` | 258 |
| `CQRV/Circuit/GradeCompose.lean` | 765 | `CQRV/Patterns/Sound.lean` | 184 |
| `CQRV/Certify/CountCert.lean` | 759 | `CQRV/Synthesis/QFT.lean` | 96 |
| `CQRV/Synthesis/Counting.lean` | 505 | `CQRV/Circuit/UnitaryChannel.lean` | 67 |
| `CQRV/Grover/AmplitudeEstimation.lean` | 500 | **total (14 modules)** | **7868** |
| `CQRV/Grover/QPEBound.lean` | 478 | | |

## 6. Deviations and open items

Deviations recorded in `docs/DECISIONS.md` (Stages 14–21) that bear on a claim, one line each:

- 2026-10-29 (14a): the solution count is decided by the kernel for n ≤ `--count-limit`
  (`hM_count`); `cert` then has no hypothesis — the M2 form `hM_card` remains for larger n.
- 2026-10-30 (14b, 14c): every n = 12 kernel-decided certificate timed out at 900 s; n = 10 took
  103 s and 11.4 GB; the default `--count-limit` is 10.
- 2026-10-30 (15b): the Grover lemma over an abstract oracle (`grover_parametric_lemma_gen`); the
  coherent certificate (`grover_certificate_coherent`) and schema `uncompute`.
- 2026-10-30 / 10-31 (16a, 16b): the front end is proved (`toNetwork_pred`) and stated in every
  `Cert.lean`; the parser, surface checker and typed-term printer remain the declared boundary.
- 2026-10-31 (17a, 17b): exact phase gates `p` / `cp` and the second record `GradeExt`; the
  Clifford+T cost of rotation gates (`rot`) is not folded into `t`.
- 2026-11-01 (18b, 18c): `qft_basis`, the AQFT bounds through Theorem 3.3b with the L2 operator
  norm; a lemma name of the spec corrected (`Real.norm_exp_I_mul_ofReal_sub_one_le`).
- 2026-11-01 (19a): ⊕ is a proved *bound* on the measured grade (`grade_append_le`,
  `grade_assembleCounting_le`), not an equality; the counting grade is therefore `composed_bound`.
- 2026-11-05 (19b): the phase-register convention (`data n` the MSB, eigenphases ±θ/π, the phase fix
  `z`) confirmed numerically to 2·10⁻¹⁴; the decoding without `bitRev`.
- 2026-11-10 (20b1, 20b2): `CountOut m a` carries the pseudo-metric induced by the estimate (a
  reflection has the same estimate; not a metric); Theorem 3.3b restated on a pseudo-metric; the
  AQFT counting certificate is not written (its bound is vacuous for m ≤ 6).
- 2026-11-12 (20b3): the compositional certificate form (blocks as literals; no kernel evaluation of
  the whole circuit); `ae_parametric_lemma_mk` (field form) because the record form exceeded the
  heartbeat limit; pattern lambdas written with projections.
- 2026-11-13 (21a1): the draft "a search request's nearest miss stays Grover" was false
  (`search_while` without `--solutions`); `matchLibrary` takes the nearest miss among the entries
  with the term's root shape. (21a2): `t.Ground` in `millerMatch_complete` is implied by
  well-formedness and kept; uniform arity is a necessary hypothesis (§3).
- 2026-11-13 (21a3): the `builder` field of `QPLP`; `target` in the unitary group; the header line
  of the counting `Cert.lean` kept until 21m (fixed here). (21a4): a non-chosen `fewLogMbu` through
  `groverCircuitFew_ok_of` (the kernel does not evaluate `groverCircuitFew` directly).

Open items, each with its destination (PHASE2_SPEC §A.9, 2026-11-15):

| Item | Destination |
|---|---|
| Measured composition exercised (counting then search with the estimated M; §A.7) | 21b1 feasibility probe, then 21b2 (route (a) or (b)) |
| Unqomp / Silq safety conditions (23b) | decided at M4, after Stage 23 |
| The SQIR / VQO comparison (Stage 29) | not run as a stage; reasons and a literature comparison at Stage 30 |
| Count selection (precision first, composed bounds) | no Phase 2 stage; Paper 1 limitation and future work |
| A budget on `grade_ext` (no mid-circuit measurement, no feed-forward) | Stages 24 and 26 (`treeCoherent` for a target without mid-circuit measurement) |
| Tracked `sorry` obligations | none (`docs/SORRIES.md` empty; `scripts/check_sorries.sh`) |

## 7. Claims for Paper 1

| Claim | Evidence | Exact scope |
|---|---|---|
| Grover search is certified end to end for the committed instances, with measured grades and exact δ | `cert` of `grover_pred_037`, `simple_alu_x0_1`, `_few`, `_coh`; `print_axioms.sh` (CI step 8); `certify_check.py` (step 22) | the network literals and IR literals of those `Cert.lean` files; `RealizesExact` with the basis POVM; the parser / surface checker / emitter outside the kernel |
| Quantum counting (amplitude estimation) is certified for the committed instance, universally in M ≥ 1 | `cert`, `cert_count` of `grover_pred_037_count`; `ae_parametric_lemma_mk` | n = 8, m = 4, exact inverse QFT, shape tree, mode mbu; ε at the stated m; the grade is a composed bound; no claim for M = 0 |
| The matcher is sound and complete, and the match set is empty or a singleton | `millerMatch_sound`, `millerMatch_complete`, `matchers_agree`, `matchLibrary_spec` | the fragment `MillerFragment` (Miller patterns with uniform arity), ground terms, well-formed substitutions, side conditions over φ's metavariables; on normal forms |
| Both patterns are instances of Definition 4.1 with a uniform `Realizes` claim | `groverSem`, `countSem`, `QPLP.Sem.realizes_of_le`; `qplpLibrary_entries` | the Grover output under the discrete metric (ε = 0); the record carries the builders and the proofs, not the CLI |
| Selection under a budget is certified | `select_spec`; `chosen_fits`, `selected` of `grover_pred_037_sel`; `select_check.py` (step 23) | the three candidates (tree, mbu), (tree, coherent), (few:log, mbu) at the request's r; the key order of (8′); search requests |
| The front end is proved | `toNetwork_pred`; `front_end` in every `Cert.lean` | typed term → network only; the parser, surface checker and typed-term printer are the declared boundary |
| Theorems 3.3a / 3.3b are proved; 3.3b is used by the AQFT variant | `measured_composition`, `coherent_composition`, `ae_parametric_lemma_aqft` | 3.3a is exercised at `grover_pred_037`, (n, M, m) = (8, 32, 5), in the form of PHASE2_SPEC §A.9 (12) (Stage 21b2): the library theorem `search_unknown_M` over `countSem` and `groverSem`, the instance's domain lemma `domain_8_32_5`, and the corollary `search_unknown_M_8_32_5` whose remaining hypotheses are decidable circuit facts; no committed composition certificate |

Claims not to make: "verified on hardware" or that any hardware run validates a certificate (the
`hardware` object checks declared figures, §5.3.1); matcher completeness beyond the implemented
fragment (uniform arity, ground terms, normal forms); optimality beyond the stated candidate space
and order; a formal cost bound for matching (Proposition 5.1 (3) is not formalized); any claim for
M = 0 in counting; that the emitted QIR / QASM is verified (translation-validated only); that the
counting grade is measured (it is a composed bound); that the AQFT variant is certified at m = 4.

## 8. Errata against report v3

Figures of report v3 (`docs/cqrv_report_revised_v3.docx`) stated in this report that differ from
the measured values. The grades (15, 134, 72, 7) and (16, 121, 60, 10), δ = 7/128 and 833/2048
agree with v3 and are not errata.

| # | Report v3 | Measured (M3) | Source |
|---|---|---|---|
| 1 | Chapter 8: `grover_pred_037` "kernel-checked in 7.2 s (measured …)" | 12.8 s kernel, 23.7 s wall (median of 5), with the front-end block, `gradeExt_eq` and `hM_count` added since (Stages 14a, 16b, 17b) | `examples/certs/grover_pred_037/certificate.json` |
| 2 | Errata item 15: second predicate "kernel check 6.4 s" | 13.0 s kernel, 23.9 s wall (median of 5) | `examples/certs/simple_alu_x0_1/certificate.json` |

Not measured, hence not stated: proof sizes or effort against SQIR / VQO (Stage 29 not run), any
timing on the GitHub runner (CI is local), and hardware figures.
