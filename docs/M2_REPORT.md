# M2 report — certified Grover pipeline (Stage 9b, 2026-10-25)

Input for report v3. Milestone M2 as revised in the Stage 5 review: **measured grades, deviations
documented**. Acceptance is `scripts/ci_local.sh` on the development machine (CI is not run
remotely). Every number below is measured by this repository; the report's figures appear only in
the errata table (§5).

## 1. What is certified

`#print axioms` (pinned toolchain `leanprover/lean4:v4.35.0`, Mathlib `56a00585…`, Physlib
`96a6bc5e…`; `scripts/print_axioms.sh` audits every named theorem of `CQRV.Certify` and both
committed certificates, blocking):

| Theorem | Report § | Axioms |
|---|---|---|
| `CQRV.Grover.grover_parametric_lemma` (realization ∧ restoration, every `r`) | §8.2–8.3, Fig. 8.1 | propext, Classical.choice, Quot.sound |
| `CQRV.Certify.grover_certificate` (its specialization) | §5.1.3, §8.4.1 | propext, Classical.choice, Quot.sound |
| `CQRV.Certify.sin_sq_odd_mul` (exact δ for every `r`) | §8.2 | propext, Classical.choice, Quot.sound |
| `CQRV.lemma_6_3_2_xor`, `CQRV.lemma_6_3_2_xor_of_le` (Lemma 6.3.2, XOR networks) | §6.3.2 | propext, Classical.choice, Quot.sound |
| `CQRV.mbu_channel_correct` (MBU on density operators) | §6.2.2 | propext, Classical.choice, Quot.sound |
| `CQRV.measured_composition_exact` (Theorem 3.3a, ε = 0) | §2.3.2 | propext, Classical.choice, Quot.sound |
| `CQRV.no_cloning_obstruction` (Theorem 3.1, concrete form) | §2.2.2 | propext, Classical.choice, Quot.sound |
| `CQRV.Matching.millerMatch_sound` (Algorithm 1) | §4.1 | propext, Classical.choice, Quot.sound |
| `CQRV.Cert.grover_pred_037.cert`, `CQRV.Cert.simple_alu_x0_1.cert` | §8.4.4 | propext, Classical.choice, Quot.sound |

Each `cert` states, for the network literal `net` and the IR literal `emitted` of its `Cert.lean`:
`RealizesExact (SearchSpec (Network.pred net n)) (basisPOVM n) (groverChannel n emitted) δ g ∧
AncRestore n a emitted (groverOp (Network.pred net n) ^ r * hadamardU n)`, under the hypothesis
`hM_card` (the solution count, §5.1.3: supplied, never decided).

## 2. The two certificates (`examples/certs/`, each with `run_report.md` / `.json`)

Post-M2 note (2026-10-26, Stage 12a): the diffusion's MCZ is now a balanced AND tree (same 7 / 5 ANDs, ⌈log₂ n⌉ levels); both certificates were regenerated: grover_pred_037 (15, 230, 72, 7) → (15, 134, 72, 7), now within the declared ibm_kyiv depth budget 200 (δ_hw still vacuous, G·p̄ = 3.90); simple_alu_x0_1 (16, 145, 60, 10) → (16, 121, 60, 10); δ, G and predicate hashes unchanged, new circuit / proof hashes in DECISIONS.md (2026-10-26, Stage 12a); the chain values below stay machine-checked as `grover_pred_037_certified_statement_chain`.

Post-M2 note (2026-10-27, Stage 12d): a third certificate, `examples/certs/grover_pred_037_few/` (`cqr certify --shape few:log`: the 2-ancilla diffusion, Khattar–Gidney 2025 §5.3 with Maslov 2016 relative-phase Toffoli pairs), is `certified (conditional on: solution_count = 32)` with grade (10, 172, 96, 2), δ = 7/128, kernel check 6.76 s kernel / 16.37 s wall, ibm_kyiv fits all budgets (δ_hw ≤ 2467/640, vacuous); its classical KG step is checked per instance by `decide +kernel` (1.53 s / 8.13 s / 40.9 s at n = 8 / 10 / 12; DECISIONS.md 2026-10-26 and 2026-10-27, Stage 12d); the tree certificates above are unchanged.

| | `grover_pred_037` (Chapter 8) | `simple_alu_x0_1` (second predicate, Table 9.2) |
|---|---|---|
| Predicate | x0 ∧ x3 ∧ x7, n = 8 | RevLib Simple ALU (`simple_alu_234.src`), bit 1 of x0, n = 6: `if op = k` chain, XOR chain |
| Status | certified (conditional on: solution_count = 32) | certified (conditional on: solution_count = 30) |
| Hypotheses | `hM_card` (M = 32, ℰ computes it); F₂ ≥ 1 (matcher); r = 2 | `hM_card` (M = 30, enumerated in the harness only); F₂ ≥ 1; r = 1 |
| Grade (w, d, t, a), measured | (15, 230, 72, 7) | (16, 145, 60, 10); oracle (16, 80, 40, 10), ĉ∧ = 10 = AND nodes |
| δ (exact) | 7/128 (success 121/128) | 833/2048 (success 1215/2048) |
| Front end | validated on 2^8 inputs | validated on 2^6 inputs |
| G (noisy operations) | 390 | 345 |
| predicate_hash | `d5f12821…819417e` | `07acc1e7…8e26c75` |
| circuit_hash | `f1331e55…db5f3705` | `93b239e4…99b2edbd` |
| proof_hash | `98299444…ce2cdd5f` | `cffe796d…a089b3f5` |
| Kernel check (median of 5) | 7.23 s kernel, 17.10 s wall | 6.37 s kernel, 16.25 s wall |

M/N = 30/64 ≈ 1/2, so Grover gives almost no advantage on this instance (r⋆ = 1); it was chosen
to exercise XOR and if end to end, not as a speed-up demonstration.

Machine: 13th Gen Intel Core i9-13900H, 20 logical CPUs, 2600 MHz (max), `LEAN_NUM_THREADS=4`,
Windows 11. Wall time includes process start and the `import CQRV` load (≈ 3.5 s). Full hashes are
in each `certificate.json`. Differential evidence (CLAUDE.md rule 9): every measurement branch of
the oracle (1024), one iteration (32768) and the full r = 1 circuit (32768) of `simple_alu_x0_1`
match the statevector harness; its success probability equals 1215/2048 in every branch
(`tests/diff/benchmark_diff.py`); the transcription equals the SyReC integer semantics on all 64
inputs.

## 3. Remaining tracked obligations (`docs/SORRIES.md`)

Post-M2 note (2026-10-25): measured_composition (Theorem 3.3a, general ε) closed in c691700; coherent_composition (Theorem 3.3b) closed in f49b39d; no sorry remains.

| Obligation | Report § | Status |
|---|---|---|
| `measured_composition` (Theorem 3.3a, general ε; `CQRV/Realizability/Composition.lean:146`) | §2.3.2 | open (`sorry`, tracked); not used by either certificate |
| `coherent_composition` (Theorem 3.3b; `CQRV/Realizability/Coherent.lean:37`) | §2.3.2, §9.3 | open; Phase III (diamond norm), not attempted |
| `synthesizeOracle_WF` (`N.WF → synthesizeOracle N = .ok C → C.WF`) | §6.3.2, §9.1.1 | planned (no `sorry`); certificates discharge `C.WF` per instance by `decide +kernel` |

Documented gaps without a row: Theorem 3.1 in categorical form (concrete form proved); dirty-ancilla
management (§8.5.3, Phase II hardening) not started; a Lean proof of `toNetwork` (replaced by the
exhaustive validation, §4).

## 4. Declared trust boundaries

* **Front end** (`trust_boundary.front_end`): "DSL → network: exhaustively validated (2^n inputs)
  by the unverified evaluator; not kernel-checked" for n ≤ 16 (both certificates), else the Stage 8b
  wording. The theorem is about `net`; `evalProgram` and `Network.pred (toNetwork …)` agree on every
  input, but both are unverified, and the parser / surface checker are shared by both sides (the
  source is bound by `predicate_hash`). The run reports therefore split stage 1 (Stage 9b review):
  1a "parser and surface checker: declared trust boundary (shared by both sides of the
  comparison)" and 1b "typed AST → network: exhaustively validated (2^n inputs)".
* **Emitter** (`trust_boundary.emitter`): QIR / OpenQASM 3 text unverified; translation-validated
  by re-parse to the IR literal (`check_emit.sh`, `certify_check.py`; llvmlite verification).
* Also outside the kernel: ℰ and the matcher (the theorem restates the instance), the
  harness-supplied M (a hypothesis of the theorem), the pinned Lean kernel and toolchain.

## 5. Report claim vs measured value (every erratum so far)

| # | Report claim | Measured / correct | DECISIONS.md entry |
|---|---|---|---|
| 1 | §6.1.4 Table 3: Grover oracle depth 21 | 27 (11 layers per TempLogicalAND compute) | 2026-10-23 "measured Grover oracle depth is 27, not 21" |
| 2 | §6.2.2 MBU listing restores the target "(reset)" | no reset in the listing; `if m: X t` added | 2026-10-23 "the §6.2.2 MBU listing has no reset" |
| 3 | §6.1.3 Table 2, a_max = 2: 4 rounds, ×8, ≤ 256 | infeasible (8 nodes need ≥ 4 pebbles) | 2026-10-23 "Table 2 rows a_max = 2 and 1 are infeasible" |
| 4 | §6.1.3 Table 2, a_max = 1: 8 rounds, ×128, ≤ 4096 | infeasible | same entry |
| 5 | §6.1.3 Table 2, a_max = 4: depth ×2 | ×1.45 (depth 144 vs 99), T = 48 | same entry |
| 6 | §7.2.2 Table 2: Grover tuple "8, 2, 3" | (8, 2, 2): AND-depth 2 | 2026-10-23 "§7.2.2 Table 2 complexity tuple" |
| 7 | §4.1.4 / §4.3.3: F₁ for both the arity and the iteration bound | F₁ arity, F₃ iteration bound, G₁… for lgg variables | 2026-10-23 "Metavariable names in φ_Grover" |
| 8 | Table 3.3 / §6.1.4: diffusion D₈ (10, 16, 28, 2) | (15, 89, 28, 7) (V1, 7 clean ancillae) | 2026-10-24 "measured diffusion and Grover grades" |
| 9 | Table 3.3 / Chapter 8: Grover slice (10, 74, 72, 2) | (15, 230, 72, 7) (t agrees) | same; 2026-10-24 "Headline grade is V1" |
| 10 | §8.5.2 / §9.5.1: kernel check 0.3 s | 7.23 s kernel / 17.10 s wall (8b: 7.43 s; 9b: 7.20 s) | 2026-10-25 "kernel-time erratum candidate" |
| 11 | §6.3.2 / §8.5.3: Theorem 3.3a "applies at the terminal measurement" | realized by the decoding POVM of `RealizesExact`; no composition step | 2026-10-24 "Theorem 3.3a at the terminal measurement: wording" |
| 12 | (plan, 9a) `synthesizeOracle_WF` without hypothesis | false (`⟨0, #[.input 5], [0]⟩`); needs `N.WF` | 2026-10-25 "Stage 9a interpretations" (7), 9a review (2) |
| 13 | (9b) §8.5.1 signature `delta_bound = 1/8 # M/N` | M/N = sin²θ; certified δ = 7/128 | 2026-10-25 "Stage 9b interpretations and findings" (6)(i) |
| 14 | (9b) §8.5.1 Stage 8, §5.3.4: "the verified emitter" | unverified emitter, declared trust boundary (as §8.5.3 says) | same, (6)(ii) |
| 15 | (9b) §9.5.1 0.3 s for the second predicate | 6.37 s kernel / 16.25 s wall (9b: 6.34 s) | same, (6)(iii) |

Also found in 9b (implementation, not report): the certificate generator overflowed `maxRecDepth`
on a 33-node network (elaborator evaluated the synthesizer); fixed by `okPayload` (DECISIONS.md
2026-10-25, Stage 9b findings (3)).

## 6. Local CI (`scripts/ci_local.sh`)

Run on the final Stage 9b tree (i9-13900H, Windows 11, Git Bash, `LEAN_NUM_THREADS=4`): **15 PASS,
0 FAIL, 4 n/a**. The n/a steps have no local counterpart: checkout (the working tree), elan
install (local toolchain), setup-python (`.venv`), apt install of llvm (`llvm-as` absent; the QIR
text is verified with llvmlite, mandatory). PASS: Mathlib cache, `lake build`, warning check,
sorry check + self-test, CLI smoke, axiom audit (blocking; both committed certificates), Python
requirements (lock) + `pip check`, simulator self-test, differential oracle test, front-end
validation (Stage 9b), golden circuits, diffusion and Grover circuit, second worked predicate
(Stage 9b), SHA3 / schema / QIR-QASM re-parse, `cqr certify` (both predicates, negative tests).
