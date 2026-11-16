# M5 report — Phase 2 complete: Tracks A, B, C certified, the release ready (Stage 30b, 2026-11-16)

Input for report v5, for the Stage 30 revision of Paper 1 and for Paper 2 (the reviewer's drafts of
30c; the author owns the final text), in the manner of `docs/M3_REPORT.md` (frozen). Milestone M5
(PHASE2_SPEC §D): Track A (counting, selection, measured composition), Track B (restoration under
measurement, Clifford ⇔ quadratic, the three regimes, the 8n − 24 bound) and Track C (the chain from
the logical certificate to the routed physical circuit, and the conditional noise theorem) are
certified; Stages 28 and 29 are not run; the release (30d) waits for the author. Every number below is
measured by this repository and names its source: a committed `certificate.json` or `manifest.json`,
the acceptance CI logs (`.lake/ci_local/<step>-*.log` of the reviewer's run of 2026-11-16 on 95f3378
plus the 30a tree, 26 PASS, 0 FAIL, 4 n/a), a committed Markdown table, or a command given here.
"Not measured" is written where nothing was measured. Nothing here is "verified on hardware": no
device was run.

Toolchain (`lean-toolchain`, `lake-manifest.json`; the `reference_configuration` of every committed
`certificate.json`): Lean `leanprover/lean4:v4.35.0`, Mathlib at the `v4.35.0` tag (`56a00585…`),
Physlib `96a6bc5e…`; machine: 13th Gen Intel Core i9-13900H, 20 logical CPUs, Windows 11,
`LEAN_NUM_THREADS=4`. The Python harness: `tests/diff/requirements.lock` (`.venv`); the hardware
tools: `hw/requirements.lock` (`.venv-hw`: qiskit 2.6.2, qiskit-aer 0.18.2, qiskit-ibm-runtime
0.52.1, numpy 2.4.6, scipy 1.17.1).

## 1. What is certified

### 1.1 Theorems and their axioms

Source: `scripts/print_axioms.sh` as CI step 8 "Axiom audit (blocking)" (211 s), and the
`#guard_msgs` on `#print axioms` of `tests/CQRVTests/*.lean` (152 distinct pinned lines; every
theorem below is pinned there unless marked ‡, in which case it is checked by step 8 through a
certificate). "Standard" means exactly `propext`, `Classical.choice`, `Quot.sound`. The eight pinned
lines with fewer axioms are listed as such; no theorem uses any other axiom (`sorryAx` and
`Lean.ofReduceBool` are rejected by the audit).

**Tracks A and the M3 base** (unchanged since `docs/M3_REPORT.md` §1.1): the certificate lemmas
`grover_certificate`, `_few`, `_few_all`, `_coherent`; `grover_parametric_lemma`, `_gen`;
`lemma_6_3_2`, `lemma_6_3_2_coherent`; `toNetwork_pred`; `measured_composition`,
`coherent_composition`; `qft_basis`, `aqft_diamond_le`; `countingCircuit_ancRestore`;
`phaseDist_eq`, `qpe_success`; `ae_parametric_lemma`, `_aqft`; `millerMatch_sound`,
`matchLibrary_spec`; `groverSem`, `countSem`; `select_spec`; the all-n restoration of the few-ancilla MCZ
(KG Theorem 5.1, Stage 13a): `mczFew_logDepth_ancRestore`, `diffusionFew_logDepth_ancRestore`, used by
`grover_certificate_few_all` with no per-instance classical check — all standard. Added since M3 (Stage 21b2):
`measured_composition_pseudo`, `measurePrepare_encode`, `search_unknown_M`, `domain_8_32_5`,
`search_unknown_M_8_32_5` (Theorem 3.3a exercised at (n, M, m) = (8, 32, 5)) — standard.

**Track B** (report §6.2, PHASE2_SPEC §B; Stages 22–23):

| Theorem | Statement | Axioms |
|---|---|---|
| `mbu_general`, `mbu_general_phase`, `mbu_channel_correct_of_general` (22a) | any phase-exact compute block, measured in the X basis and corrected by a phase implementation of the same function, restores its ancilla; `mbu_channel_correct` re-derived | standard |
| `isQuadratic_iff_deriv_affine`, `phaseCircuitQuad_phaseImpl`, `mbu_quadratic`, `clifford_iff_quadratic` (22b) | the MBU correction is Clifford iff the function has degree ≤ 2 over 𝔽₂ | standard |
| `gateU_isClifford`, `isCliffordDiag_of_tensor`, `mbu_wf_forces_quadratic`, `mbu_exactly_quadratic` (22c) | every IR Clifford gate is Clifford on the register; a well-formed MBU circuit exists for `f` iff `f` is quadratic | standard |
| `ancRestore_list`, `ancRestoreMix_of_kraus`, `mbu_uncorrected`, `AncRestore.widen`, `AncRestore.comp_widen` (23a) | block lists restore; restoration under measurement with a mixed data action; MBU without its correction dephases; ancilla reuse by widening | standard |
| `ancRestoreDirty_of_kraus`, `AncRestoreDirty.toClean/.comp/.toCond`, `reset_not_dirty`, `AncRestoreCond.toClean/.comp` (23b) | the three regimes and the strict hierarchy dirty ⇒ conditionally clean ⇒ clean | standard |
| `Inv.cond_value` (23b, `CQRV/Grover/KGRegime.lean`) | the KG invariant as the bridge to the conditional regime | `propext` |
| `problem1_T_lower_bound`, `planB_valid` (23c) | 8n − 24 on KG Problem 1 schedules under the stated cost model; candidate B attains it for n = 6 … 12 (`planB_cost`), 8n − 20 at n = 4, 5 | standard |

**Track C** (report §5.3, §9.1.1, §2.3.2, §6.6; PHASE2_SPEC §C; Stages 24–27):

| Theorem | Statement | Axioms |
|---|---|---|
| `decomp_sound`, `translate_sound`, `realizes_translate` (26a) | the basis table is sound entry by entry; the translation of a well-formed circuit is well formed with the same channel; `Realizes` transfers | standard |
| `channelDenote_relabel`, `ud_swapEntry`, `channelDenote_embed`, `nAnc_translate` (26b1) | relabeling, the routing SWAP and the embedding into the compact register as channel equalities | standard |
| `gateK_comm_of_disjoint`, `krausOps_reorder`, `krausOps_swap_migrate` (26b2) | gates on disjoint qubits commute; the dependency-queue reordering preserves the Kraus operators | standard |
| `applyWitness_sound`, `AncRestore.phys`, `realizes_phys`, `gadgetPhys_correct` (26b3) | the routed circuit on the embedded input is the embedded logical output at the final layout; `Realizes` transfers to the physical circuit | standard |
| `applyWitnessQ_ok`, `layOf_layPerm`, `embed_zero` (26c1) | the linear check implies the witness check; the layout permutation; all-|0⟩ is the embedded |0⟩ | standard |
| `selectPhys_spec`, `selectNoise_spec` (26c2b, 27b) | selection by a grade component or by the noise bound is admissible and minimal | standard |
| `channelDenote_eq_steps` (27a) | the step semantics with the classical register equals `channelDenote` | standard |
| `diamondDist_steps_le`, `diamondDist_mix_le` (27a) | the perturbation bound of a composition; `‖(1 − p)Φ + pΦ' − Φ‖⋄ ≤ 2p` on the full register | standard |
| `noisy_realization`, `phys_noisy` (27a) | a realization survives noisy steps with `δ + ½ Σ ηᵢ`; the instance on the routed circuit | standard |
| `phys_noisy_stochastic`, `phys_noisy_inst_of`, `phys_noisy_channel_stochastic` (27b) | the stochastic premise at basis operations: for every choice of the arbitrary channels the noisy physical channel realizes the specification with `δ + Σ p_g + Σ r_j`; the instance form with the exact bound; the channel form | standard |
| `emitted_eq` (each `PhysCert.lean`), `c_eq` (`mbu_gadget_torino/NoiseCert.lean`) ‡ | the trusted links: the artifact's logical circuit is the certified `emitted` / is `mbuCircuit` | none |
| `phys_realizes`, `phys_noisy_inst`, `gadget_noisy` (each committed physical / conditional certificate) ‡ | the instances of the theorems above | standard |

The other pinned lines with fewer axioms than standard: `Gate.qubitsOk_shiftData` and
`Grade.fitsPartial_ofGrade` (`propext`, `Quot.sound`), `Grover.mczFew8_WF`, `Grover.diffusionFew8_WF`,
`Grover.grover037_grade_chain` (`propext`), `Grover.diffusion_ok_chain`, `cone_closed` (`propext`,
`Quot.sound`), `Certify.except_eq_ok_okPayload` (`propext`), `Certify.except_ok_of_check` (none).

### 1.2 The committed certificates

**Logical** (`examples/certs/<dir>/certificate.json`; `cert` is `RealizesExact (SearchSpec (Network.pred
net n)) (basisPOVM n) (groverChannel n emitted) δ g ∧ AncRestore n a emitted …`, no hypothesis — the
solution count is decided by the kernel; the counting `cert` is universal in M ≥ 1):

| Directory | Pattern; instance | `grade` (w, d, t, a); kind | `grade_ext` (2Q, T-depth, rot, meas, ff) | δ | Kernel (`kernel_check`) |
|---|---|---|---|---|---|
| `grover_pred_037` | Grover; n = 8, M = 32, r = 2; tree, mbu | (15, 134, 72, 7); measured | (126, 39, 0, 18, 36) | 7/128 | 12.8 s kernel, 23.7 s wall (median of 5) |
| `grover_pred_037_coh` | Grover; tree, coherent | (15, 200, 144, 7); measured | (216, 74, 0, 0, 0) | 7/128 | 23.3, 34.2 (median of 5) |
| `grover_pred_037_few` | Grover; few:log, mbu | (10, 172, 96, 2); measured | (106, 77, 0, 8, 16) | 7/128 | 11.2, 22.1 (median of 5) |
| `grover_pred_037_sel` | Grover; `--budget 12,200,100,8 --prefer depth` → few:log, mbu | (10, 172, 96, 2); measured | (106, 77, 0, 8, 16) | 7/128 | 25.4, 36.3 (single run) |
| `grover_pred_037_count` | Count; n = 8, m = 4, M = 32; exact inverse QFT, mbu | (20, 1388, 660, 8); composed bound | (1161, ≤ 660, 6, 165, 330) | 1 − 8/π² ≈ 0.189431 (ε ≈ 0.168426) | 18.6, 29.8 (single run) |
| `simple_alu_x0_1` | Grover; n = 6, M = 30, r = 1; tree, mbu | (16, 121, 60, 10); measured | (137, 28, 0, 15, 30) | 833/2048 | 13.0, 23.9 (median of 5) |
| `hw_n2` | Grover; n = 2, M = 1, r = 1; tree, mbu | (3, 32, 8, 1); measured | (14, 6, 0, 2, 4) | 0 | 0.28 s kernel, 11.2 wall (single run) |
| `hw_n3` | Grover; n = 3, M = 1, r = 2; tree, mbu | (5, 110, 32, 2); measured | (56, 23, 0, 8, 16) | 7/128 | 2.5, 13.6 (single run) |
| `fr_n2_tree_coherent_rb` | Grover; n = 2, M = 1, r = 1; tree, coherent | (3, 46, 16, 1); measured | (24, 12, 0, 0, 0) | 0 | 0.38, 10.7 (single run) |
| `fr_n3_tree_coherent_rb` | Grover; n = 3, M = 1, r = 2; tree, coherent | (5, 164, 64, 2); measured | (96, 44, 0, 0, 0) | 7/128 | 4.1, 14.3 (single run) |
| `fr_n3_fewlog_mbu` | Grover; n = 3, M = 1, r = 2; few:log, mbu | (5, 86, 24, 2); measured | (44, 17, 0, 6, 12) | 7/128 | 1.4, 11.6 (single run) |

The M3 figures (the first six rows) are unchanged. `fr_n2`/`fr_n3` are the frontier family
(`examples/frontier/fr_n<k>.cqr`, Grover on k ANDs); `hw_n2`/`hw_n3` have the same circuits as the
tree-mbu members of that family. Schema 1.10.0 (1.11.0 for the selection certificate).

**Physical and conditional** (`examples/certs/<dir>/manifest.json`, schema 1.1.0; `PhysGrade` at the
feed-forward latency L = 0 and 1000 ns; the kernel times from the CI logs of steps 29 and 30):

| Directory | Artifact (target) | `PhysGrade` at L = 0: qubits, 2Q, mid-meas, ff, depth (ns) | 25a bound `p = r` | `noiseBound` δ' | Status words | Kernel (s) |
|---|---|---|---|---|---|---|
| `grover_pred_037_torino` | grover_pred_037 tree mbu (FakeTorino) | 16, 315, 18, 624, 33 740 (43 740 at L = 1000) | 2.4495 (vacuous) | — (26c2 certificate; no noise block) | `logical_certified, hardware_compatible, physical_translation_validated`; emulator run "vacuous bound, not tested" | 53 |
| `hw_n2_torino` | hw_n2 tree mbu (FakeTorino) | 3, 26, 2, 88, 5 848 (7 848) | 0.1500 | **0.1793** | the three above + `noise_conditional, emulator_validated` | 13 |
| `hw_n3_torino` | hw_n3 tree mbu (FakeTorino) | 5, 101, 8, 184, 22 292 (30 292) | 0.6484 | **0.7521** | the same five | 20 |
| `mbu_gadget_torino` | mbu_gadget (FakeTorino), channel form | 3, 13, 1, 44, 3 196 | 0.0860 | **0.0995** | `hardware_compatible, physical_translation_validated, noise_conditional`; no run recorded; logical statement `mbu_channel_correct` | 11 |
| `fr_n3_tree_coherent_rb_torino` | fr_n3 tree coherent, routing (b) (FakeTorino) | 5, 96, 0, 0, 11 008 | 0.4893 | **0.5962** | the four (no run recorded) | 23 |
| `fr_n3_fewlog_mbu_torino` | fr_n3 few:log mbu (FakeTorino) | 5, 89, 6, 264, 18 372 (24 372) | 0.6718 | **0.7776** | the four (no run recorded) | 18 |
| `fr_n2_tree_coherent_rb_washington` | fr_n2 tree coherent, routing (b) (FakeWashington) | 3, 24, 0, 0, 10 503 | 0.1706 | **0.2110** | the four (no run recorded) | 11 |

No committed instance clamps (`clamped: false` everywhere). The emulator comparison of a conditional
certificate applies 25b's criterion to the recorded run with the recorded margin
(`threshold' = threshold + δ_hw − δ'`): hw_n2 p̂ = 3527/4000 vs 0.8014 and hw_n3 p̂ = 2361/4000 vs
0.2286 pass (`docs/hw_runs/`); the emulator's noise model is not of the premises' form, so this is a
sanity check, not evidence for (P-stoch).

**The per-instance check files** (`examples/hw_checks/<artifact>/Check.lean`, fifteen; `recon` by
`rfl`, `phys_channel`, `phys_zero`; CI step 28 log): mbu_gadget 10 s, mbu_gadget_wrapped 11,
hw_n2_tree_mbu 11, hw_n3_tree_mbu 14, fr_n2_tree_coherent_rb (Washington) 11,
fr_n3_tree_coherent_rb 15, fr_n3_fewlog_mbu 14, grover_pred_037_tree_mbu 30, _tree_coherent (Torino)
30, _tree_coherent (Washington) 19, _fewlog_mbu 21, simple_alu_x0_1_tree_mbu 30, _tree_coherent
(Torino) 30, _tree_coherent (Washington) 18, _fewlog_mbu 27 — all with the standard three axioms;
the peak memory per file (1.8–4.1 GB) is in `examples/hw_checks/README.md`. **The selections**
(`examples/hw_select/*/Select.lean`, CI step 29 log): grover_pred_037 on Torino 22 s, on Washington
8 s; simple_alu_x0_1 on Torino 31 s, on Washington 10 s.

### 1.3 The feasibility frontier

`docs/hw_frontier/FRONTIER.md` (generated by `scripts/frontier.py` from `frontier.json`; 30 rows; r =
r⋆ as `cqr` chooses it). The frontier — the largest n of the family with `noiseBound` < 1 — per
(target, mode, routing (a) full coupling map / (b) edges of error ≥ 1/2 removed):

| Target | Mode | (a) | (b) |
|---|---|---|---|
| FakeTorino | tree mbu | n = 3, 0.7521 | n = 3, 0.9590 |
| FakeTorino | tree coherent | n = 3, 0.7415 | n = 3, **0.5962** |
| FakeTorino | few:log mbu | n = 3, **0.7776** | n = 3, 0.8345 |
| FakeWashington | tree coherent | n = 2, 0.2278 | n = 2, **0.2110** |

Every FakeTorino series is vacuous from n = 4 (1.60–2.19) and every FakeWashington series from n = 3
(1.18–1.24). The idle-exposure diagnostic (each used qubit's idle time under the ASAP schedule over
its T2; reported only) is 0.05–0.38 at the frontier rows and above 1 at n = 5.

## 2. The chain, end to end

The logical pipeline is `docs/M3_REPORT.md` §2 (unchanged). Track C adds, for a routed circuit:

| Step | Tool (untrusted) | Lean (kernel-checked) | Where |
|---|---|---|---|
| target | `hw/target.py` (Qiskit fake backend → `HardwareTarget` JSON) | the snapshot hash (SHA3-256) re-checked | `cqr hw capabilities`; CI step 24 |
| translation | `hw/decomp.py` (the basis table) | `decomp_sound`, `translate_sound`; the Lean table equals the Python table | CI step 26 |
| routing | `hw/transpile.py` (`SabreLayout` alone; the witness) | `applyWitness_sound`; per instance `recon` by `rfl`, `edges_ok`, `phys_channel` | `cqr hw check`; CI step 28 |
| realization | — | `phys_realizes` through `emitted_eq`; `PhysGrade` by `decide +kernel` | `cqr hw certify`; CI step 29 |
| noise | `hw/noisebound.py` (mirror) | `noiseBound` by the kernel; `phys_noisy_inst` for every choice of the arbitrary channels | `cqr hw noisecert`; CI step 30 |
| emulation | `hw/run.py` (Aer, the fake's noise model) | nothing: reported, compared at δ' with the recorded margin | `docs/hw_runs/`; CI step 27 |

The vocabulary of a certificate manifest: `meaning_physical_translation` (the physical statement: on
an ideal device with these gates and this connectivity, started from all-|0⟩, the routed circuit
realizes the specification with the certified δ) and `noise.meaning` (the conditional statement: under
(P-cal), (P-stoch), (P-ro), (P-idle), the device's success probability is at least 1 − δ'; the premises
are assumptions about the device, not facts proved here).

## 3. The CI (26 steps)

`scripts/ci_local.sh` (local; CI is not run remotely), the reviewer's acceptance run of 30a
(2026-11-16, `.lake/ci_local/`): **26 PASS, 0 FAIL, 4 n/a** (steps 1, 2, 9, 20 have no local
counterpart). Times as reported in that run; a dash means the step took well under a minute and its
time was not reported individually (the M3 run, `docs/M3_REPORT.md` §5.1, has those steps at 0–8 s
except step 15 at 190 s, 18 at 143 s, 19 at 66 s, 21 at 67 s, 3 at 198 s).

| Step | Name | Time (s) |
|---|---|---|
| 3 | Fetch Mathlib cache | — |
| 4 | lake build | — |
| 5 | Warning check | — |
| 6 | Sorry check (+ self-test) + layering check | 91 |
| 7 | CLI smoke | 127 |
| 8 | Axiom audit (blocking) | 211 |
| 10–14 | Python requirements; simulator self-test; differential oracle test; front-end validation; golden circuits | — |
| 15 | Diffusion and Grover circuit | — |
| 16–19 | Few-ancilla MCZ; QFT / AQFT; counting circuit; second worked predicate | — |
| 21 | SHA3, schema, QIR / QASM re-parse | — |
| 22 | cqr certify (both predicates, few:log, negative tests) | 680 |
| 23 | Certified selection | 152 |
| 24 | Hardware target | 18 |
| 25 | Hardware lowering | 61 |
| 26 | Hardware transpile (schema, byte-identical reproduction, ideal equivalence) | 122 |
| 27 | Hardware runs | 37 |
| 28 | Hardware checks (fifteen `Check.lean`) | 298 |
| 29 | Physical certificate (+ four selections) | 137 |
| 30 | Noise certificates (eleven Lean files, three Python checks) | 164 |

The pass mark grew from 19 (M3) to 26 with the seven hardware steps. Step 22 ranges 675–1038 s across
the Stage 26–30 runs depending on machine load (DECISIONS.md, 27a and 27b2 reviews).

## 4. Structure

Twelve Lean packages (`git ls-files 'CQRV/<pkg>/*.lean' | xargs cat | wc -l`, 2026-11-16): Grades
425 lines (5 files), Realizability 1 150 (9), Patterns 705 (3), DSL 1 353 (10), Matching 2 662 (8),
Circuit 10 177 (17), Synthesis 3 175 (12), Certify 2 937 (11), Emit 281 (3), Grover 7 902 (13),
Hardware 7 139 (16), Noise 1 208 (4) — 39 114 lines in 111 modules; `Apps/cqr/Main.lean` 1 716;
tests 37 files, 6 032 lines; Python tools and checks 44 files, 11 738 lines. The `cqr` executable's
import closure is 62 CQRV modules with the external roots `Lean` and `Mathlib` only (no Physlib): the
certifying compiler is Physlib-free; the semantics and the theorems are Physlib-side.

The layering rule enforced in CI (step 6, `scripts/check_layering.sh`): no module of `Circuit` or
`Synthesis` imports a module of `Grover`. Nine other upward edges against the order of CLAUDE.md's
layout are documented as by design: `Certify/Specialize` → `Grover.Instance`, `Grover.MczFew`,
`Grover.MczFewAll` (the specialization of the Grover lemma); `Circuit/QFTCorrect` → `Synthesis.QFT`
and `Circuit/Restoration` → `Synthesis.Oracle` (the correctness proofs import the synthesizer they are
about); `Patterns/Basic`, `Patterns/Select` → `Certify.Basic` and `Patterns/Sound` → `Grover.Lemma`,
`Grover.AmplitudeEstimation` (the library's soundness is proved against the lemmas). The
kernel-evaluable few-ancilla schedule is one definition, `CQRV.Synthesis.FewScheduleK.planK`
(`Grover.FewSchedule.planK` and `Synthesis.Problem1.planK` are aliases).

## 5. Open items

| Item | Status (source) |
|---|---|
| Clean ⇒ Cond(true) (the clean regime as the conditional regime under `true`), `AncRestoreDirty.widen` (the dirty widening) | open; remarks for Paper 2 (DECISIONS.md, M4 review 2026-11-15; PHASE2_SPEC §B.3) |
| The all-n forms of 23c (`planB_cost` / `planB_valid` for every n) | open; proved for n = 4 … 12 (`planB_cost`, `planB_cost_small`) |
| KG Theorem 5.1 for every n (the few:log MCZ restores) | **proved** (Stage 13a: `mczFew_logDepth_ancRestore`, `diffusionFew_logDepth_ancRestore`, `grover_certificate_few_all`); the `ladder` variant is not certified |
| Commutation of blocks on disjoint qubits | **closed** by 26b2 (`gateK_comm_of_disjoint`, `krausOps_reorder`; DECISIONS.md, 27c review) |
| Count selection (precision first, composed bounds) | no Phase 2 stage; Paper 1 limitation and future work (PHASE2_SPEC §A.9 (4)) |
| Proposition 5.1 (3), the cost bound of matching | not formalized (`docs/M3_REPORT.md` §3) |
| Tracked `sorry` obligations | none (`docs/SORRIES.md`: 0 tracked; `scripts/check_sorries.sh`) |
| Stage 28, device runs | not run, by the author's decision of 2026-11-16 (PHASE2_SPEC §D.1) |
| Stage 29, the SQIR / VOQC comparison | not run; `docs/STAGE29_NOTE.md` gives the reason and a literature comparison (PHASE2_SPEC §A.9 (3), §D.2) |

## 6. Claims

### 6.1 Paper 1 (Tracks A and C)

| Claim | Evidence | Exact scope |
|---|---|---|
| Grover search and quantum counting are certified end to end for the committed instances, with measured grades and exact δ (counting: a composed bound) | the eleven logical certificates (§1.2), the axiom audit (step 8), `certify_check.py` (step 22) | the network and IR literals of those `Cert.lean`; `RealizesExact` with the basis POVM; the parser, surface checker and emitter outside the kernel; the counting grade is a bound |
| The matcher is sound and complete and selection under a budget is certified | `millerMatch_sound`, `millerMatch_complete`, `matchLibrary_spec`; `select_spec`; `grover_pred_037_sel` (step 23) | `MillerFragment` (uniform arity), ground terms, normal forms; the three candidates at the request's r |
| Theorem 3.3a is exercised | `search_unknown_M_8_32_5` | (n, M, m) = (8, 32, 5); a library theorem, no committed composition certificate |
| **For a routed circuit on a hardware description, the whole chain is checked by the kernel**: translation, routing, the instance facts, the realization transfer, the physical grade | `translate_sound`, `applyWitness_sound`, the fifteen check files (step 28), `phys_realizes` in the seven physical / conditional certificates (steps 29, 30) | the two fake backends' shipped snapshots; Qiskit untrusted everywhere; the witness, not the transpiler, is checked; the feed-forward latency is a stated assumption |
| **The noise statement is a theorem conditional on four named premises**, and six committed instances carry it with an exact δ' | `phys_noisy_stochastic`, `phys_noisy_inst_of`; `phys_noisy_inst` / `gadget_noisy` in the six conditional certificates; `noiseBound` = `hw/noisebound.py` on all artifacts (step 30) | (P-cal) a shipped snapshot from a past date; (P-stoch) the Pauli reading `p = min 1 ((d+1)/d · r)`, stated on the full register; (P-ro); (P-idle); for every choice of the arbitrary channels |
| The conditional bound is non-vacuous only for tiny instances on these calibrations | `FRONTIER.md`: δ' < 1 up to n = 3 ANDs on FakeTorino (0.60–0.78), n = 2 on FakeWashington (0.21); the 8-qubit `grover_pred_037` at 2.90 | the family `fr_n2..7`, three modes, two routings, r = r⋆; the fakes' snapshots |
| The emulation agrees with the conditional bound where it is non-vacuous | `docs/hw_runs/` (hw_n2 p̂ 0.8818, hw_n3 0.5903, the wrapped gadget 0.8995); the comparison at δ' in the manifests | a sanity check: Aer's noise model from the fake is not of the (P-stoch) form; no evidence for the premise |

**Claims not to make**: "verified on hardware" (no device was run; the emulator is not a device); that
any run validates a certificate or a premise; that (P-stoch), (P-ro), (P-idle) or (P-cal) hold of a
device (they are hypotheses, named in every manifest); useful problem sizes on these calibrations (the
frontier is n = 3 / n = 2); that the emitted QIR / QASM or `physical.qasm` is verified (translation-
validated by re-parse only); matcher completeness beyond the fragment; a formal matching cost bound;
that the counting grade is measured; anything about M = 0 in counting; that the fakes' calibrations are
live or current.

### 6.2 Paper 2 (Track B)

| Claim | Evidence | Exact scope |
|---|---|---|
| Measurement-based uncomputation restores its ancilla for any phase-exact compute block with a phase correction | `mbu_general`, `mbu_general_phase` (22a) | the IR's semantics; the correction is a phase implementation of the same function |
| The correction is Clifford iff the function is quadratic over 𝔽₂, and the IR admits exactly those | `clifford_iff_quadratic`, `mbu_exactly_quadratic` (22b, 22c) | the IR's `ifBit` admits Clifford gates only (`Gate.bitOk`) |
| The restoration algebra: block lists, mixed data actions, widening; the three regimes with a strict hierarchy | 23a, 23b theorems (§1.1) | density-operator semantics; the regimes as stated (`AncRestoreDirty` on every state, `AncRestoreCond` as a subspace regime) |
| The 8n − 24 bound on KG Problem 1 schedules under the stated cost model, attained by candidate B for n = 6 … 12 | `problem1_T_lower_bound`, `planB_cost` (23c) | the P1 model (`P1State`, `P1Op`, `cost`); n = 4, 5 give 8n − 20; the all-n form is open |
| The few-ancilla (few:log) MCZ restores its two ancillae for every n (KG Theorem 5.1) | `mczFew_logDepth_ancRestore`, `diffusionFew_logDepth_ancRestore` (13a); `grover_certificate_few_all` | the `.logDepth` variant; the `ladder` variant is not certified (classical step checked at n = 8 only) |
| Clifford+T and feed-forward accounting of the certified circuits | `grade_ext` of every certificate (§1.2) | measured by the scheduler; `rot` not folded into `t` |

**Claims not to make**: the `ladder` variant's restoration as proved (it is not certified; only
`.logDepth` is); the Unqomp / Silq safety conditions as formalized (23b was not run as a stage); the
dirty widening or Clean ⇒ Cond(true) as proved.

## 7. Deviations since M3

One line each, from `docs/DECISIONS.md` (Stages 21b–30a); the ones that bear on a claim:

- 2026-11-15 (21b1, 21b2): measured composition exercised as a library theorem at (8, 32, 5) with an
  honest second grade (g2 = (15, 794, 432, 7) at r = 12); no composition certificate.
- 2026-11-15 (22a): a degree-3 correction is not expressible in the IR (`ifBit` wraps Clifford only);
  the Clifford corollary follows in 22b/22c.
- 2026-11-15 (23b): conditionally clean is a subspace regime; the KG invariant is a bridge lemma only
  (`Inv.cond_value`, `propext`).
- 2026-11-15 (23c): the task's n-range corrected — 8n − 24 holds for n = 6 … 12, 8n − 20 at n = 4, 5.
- 2026-11-15 (24c): every worst-case bound is vacuous on both fakes (edges with error 1.0); the physical
  bound of 25a is non-vacuous for the small instances only.
- 2026-11-16 (26a): the task's phase form for the `h` entry was false; `irPhase` corrected.
- 2026-11-16 (26b1): `translateCircuit_nAnc` is false in general (counterexample `⟨1, [alloc (anc 3)]⟩`);
  `nAnc_translate` with `ancCovered`.
- 2026-11-16 (26b3): two checks added to the witness check as its definition (initial layout `Nodup`;
  a block's SWAPs compose to the identity — counterexample (0 1)(1 2)(2 0)).
- 2026-11-16 (26c1): the lockstep pass cut the 2 541-gate reconstruction from 8.9 GB to 4.1 GB.
- 2026-11-16 (27a): the stochastic premise is stated on the full register, so `diamondDist_mix_le`
  needs no tensor-stability lemma (the roadmap's fallback became the main route).
- 2026-11-16 (27a review): the premise attaches to basis operations, not IR gates (`sx` expands to
  `h, s, h`).
- 2026-11-16 (27b): `PhysGrade` and `PhysCand` are frozen by committed literals, so the `noise`
  preference is `selectKey` / `selectNoise`, not a `PhysPref` constructor.
- 2026-11-16 (27b2): the emulator comparison uses the recorded margin (the exact one is irrational);
  `certificate_json: null` artifacts are linked by `circuit_hash`; a long list of `p / q` literals
  exhausts the elaborator's heartbeats (`mkRat` literals instead).
- 2026-11-16 (27c): the artifact schema needed v1.1.0 for `routing`, caught by CI step 26 — the lesson:
  run the whole CI step, not the tool.
- 2026-11-16 (30a): no schema file governs the certificate manifests; their own `schema_version` is 1.1.0.

## 8. Errata against report v3

The two errata of `docs/M3_REPORT.md` §8 stand (the kernel times of Chapter 8 and errata item 15 are
12.8 s and 13.0 s kernel, medians of 5). No new erratum: Track C has no counterpart in report v3
beyond §9.1.1 and §9.3 (Phase III), whose statements this report's §1 and §6 replace with measured
ones. Not measured, hence not stated: any device figure (Stage 28 not run), proof sizes or effort
against SQIR / VOQC (Stage 29 not run; `docs/STAGE29_NOTE.md`), any timing on the GitHub runner (CI is
local).
