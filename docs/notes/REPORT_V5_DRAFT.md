# Report v5: a draft for the author (Stage 30c)

Written by the reviewer on 2026-11-16, under the author's delegation, for the author's approval.
This is not the report's text. It is a chapter-by-chapter plan of what report v5 adds to or
changes in report v3 (`docs/cqrv_report_revised_v3.docx`). The sources are `docs/PHASE2_SPEC.md`,
`docs/DECISIONS.md`, `docs/M3_REPORT.md` and `docs/M5_REPORT.md`. Every claim names its theorem or
file.

**v4 was not read.** `docs/cqrv_report_revised_v4.docx` is the author's and was not opened. Where v4
already contains a change listed here, the item reduces to a check.

**How to use this file:**
- Each section lists the v5 changes as **add** (new material), **revise** (v3 text that changes)
  or **keep** (unchanged, named for completeness).
- The rule of the project holds: the report is the specification. Where Phase 2 departed from v3,
  v5 states the departure and its reason.

---

## 1. Introduction

- **Revise §1.3 (roadmap).** Phase 2 adds three tracks to the Grover vertical slice:
  - **Track A**, a second problem class: amplitude estimation, quantum counting and certified
    selection;
  - **Track B**, a theory of restoration under measurement;
  - **Track C**, a hardware backend: Lean-checked translation validation, the physical grade, and
    conditional noise certificates.

  The roadmap table gains Chapters 11 (Track B) and 12 (Track C), or appendices; this is the
  author's choice.
- **Add one paragraph on the trust boundary as it stands at M5:**
  - **The kernel checks:** every certificate theorem, every per-instance hardware fact, and the
    noise bound's arithmetic.
  - **Untrusted:** the parser, the surface checker, the printers, Qiskit and Aer.
  - **Premises:** (P-cal), (P-stoch), (P-ro), (P-idle) and the feed-forward latency.
  - **Never claimed:** "verified on hardware", in any output.

## 2. Formal correctness framework

- **Keep** Definitions 2.1–2.2 (`Realizes`, `RealizesExact`).
- **Add, after §2.1: pseudo-metric output spaces.** Amplitude estimation's output type is only a
  pseudo-metric space. `coherent_composition_pseudo` and `measured_composition_pseudo` state
  Theorems 3.3a and 3.3b there with the same proofs.
- **Add to §2.3: Theorem 3.3a exercised** (21b1–21b2):
  - `search_unknown_M` at (n, M, m) = (8, 32, 5) composes counting with search by
    `measured_composition_pseudo`;
  - measure-and-prepare is a channel (`Realizability/MeasurePrepare.lean`, through the Choi
    matrix);
  - the honest grade of the search stage over every branch is (15, 794, 432, 7) at r = 12, and
    the composite is (21, 3656, 1796, 8);
  - **no composition certificate** is generated (decision of 2026-11-15).
- **Add to §2.3: Theorem 3.3b with a real η.** `aqft_diamond_le`: dropping the rotations beyond
  kmax costs η_aqft = 4πm / 2^kmax in the diamond distance. `ae_parametric_lemma_aqft` uses it.
- **Add §2.4: the noise theorem**, cross-referenced from Chapter 12:
  - the stated property is now a theorem: the fixed-reference diamond distance composes on one
    space (`diamondDist_precompose_le`, `diamondDist_steps_le`);
  - the stochastic premise costs 2p on the full register (`diamondDist_mix_le`), so no tensor
    stability is needed;
  - `noisy_realization`: δ + ½ Σ η_i.

## 3. Resource-graded refinement type system

- **Add to §3.1: `GradeExt`** (two-qubit count, T-depth, rotation count, measurements,
  feed-forward), stated in every certificate as `gradeExt_eq`. `Grade` itself is unchanged.
- **Add to §3.1: grade composition** (19a): `grade_append_le` (⊕ of Table 3.1), its n-fold form
  and the `GradeExt` analogue. Compositional certificates label the whole grade
  `composed_bound` (§5).
- **Revise §3.1.3 (hardware profiles as a change of base).** v3's change of base becomes the
  physical grade `PhysGrade`: physical qubits, two-qubit count, mid-circuit measurements,
  feed-forward count, the exact ASAP wall-clock depth at a named feed-forward latency, and the
  physical bound. It is computed in Lean (`Hardware/PhysGrade.lean`), equal to a Python mirror,
  and evaluated by the kernel in each physical certificate.
- **Add to §3.3: selection under a budget.**
  - `Patterns/Select.lean` (21a4) chooses among certified candidates under a budget, with a
    correctness theorem.
  - `Hardware/SelectPhys.lean` (`selectPhys_spec`; `selectKey` with `selectKey_spec`, of which
    `selectPhys` and `selectNoise` are instances) does the same by a physical component.
  - On a target without feed-forward only coherent uncomputation is admissible.
- **Revise Table 3.5 (the Kyiv depth check).** The δ_hw remark of v3 erratum 10 becomes the
  conditional bound of §2.4 and Chapter 12. For the running example it stays vacuous (2.9).

## 4. Pattern matching and decidability

- **Add to §4.1: the second library entry, Count** (21a1–21a3):
  - `--problem count --precision m`;
  - `QPLP.Sem` and the uniform soundness claim (`Patterns/Sound.lean`);
  - `cqr certify --problem count`.
- **Add to §4.2: completeness of the matcher** (21a2, `Matching/Complete.lean`):
  - the E2 theorems;
  - E3, proved non-match outputs;
  - E4, kernel examples;
  - the nearest-miss rule: the closest entry among those with the term's root shape, with the
    class excluded (21a1 review).
- **Keep** the anti-unification and repair hints of §4.3.

## 5. Certification architecture

- **Add to §5.1: the kernel's ceilings, measured** (14b, 18a):
  - the flat literal is memory-bound at about 750 instructions on 16 GB;
  - the 14b failure is attributed to `grade_eq` (the `Array.push` chain), not `emitted_ok`;
  - the decision: compositional certificates (blocks ≤ 600 instructions, each with an exact
    `grade_eq`).
- **Add to §5.2: the front end proved** (16a–16b). `toNetwork_pred`, and in every certificate
  `front_end : ∀ x, evalProgram prog x = Network.pred net n x`, kernel-checked. The parser,
  checker and literal printer remain the declared boundary.
- **Add §5.4: physical and conditional certificates**, cross-referenced from Chapter 12:
  - the status words `logical_certified`, `hardware_compatible`,
    `physical_translation_validated`, `noise_conditional` and `emulator_validated`;
  - the manifest vocabulary `meaning_physical_translation` and `noise.meaning`;
  - native evaluation (`native_decide`, `Lean.ofReduceBool`) is never a check, so the axiom audit
    stays at three axioms.
- **Revise §5.3 (export).** QIR / OpenQASM 3 of `p` and `cp` (17b). The physical QASM is printed
  from the validated physical circuit, by an unverified printer. Schema versions are given up to
  their final values (M5_REPORT).

## 6. Oracle synthesis and ancilla management

- **Add to §6.1: exact phase gates `p k` and `cp k`** (17a), and **QFT / AQFT** (18b–18c):
  - `qft_basis`;
  - `aqft_opNorm_le`;
  - `channelDenote_of_unitary`;
  - `diamondDist_ofUnitary_le`.
- **Add to §6.1.4: the coherent uncomputation mode** (15a–15b), with Lemma 6.3.2 in both modes and
  `grover_parametric_lemma_gen`.
- **Add §6.4: restoration under measurement.** This is Track B, the summary of Chapter 11:
  - `mbu_general`;
  - `clifford_iff_quadratic`;
  - `mbu_exactly_quadratic`;
  - the restoration algebra and the three regimes;
  - `problem1_T_lower_bound` (8n − 24).

## 7. The input DSL and specification extraction

- **Add:** `--problem` / `--precision` (21a1), and the scoping predicate `prog.scoped` of the front
  end (16a).
- **Keep** the rest.

## 8. The Grover vertical slice

- **Keep** the slice: (15, 134, 72, 7) with the balanced-tree diffusion, as v3 already says.
- **Add §8.6: the counting slice** (19–20):
  - `countingCircuit` with restoration in the circuit's own factors (`countingCircuit_ancRestore`,
    `U_count` in tensor form);
  - `phaseDist_eq` and `qpe_success` (8/π²) for every `GroverData`, M = 2ⁿ included;
  - `ae_realizes` and `ae_parametric_lemma` / `_aqft`;
  - the certificate `examples/certs/grover_pred_037_count`.
- **Add §8.7: the slice on hardware** (from Chapter 12):
  - `examples/certs/grover_pred_037_torino`;
  - `phys_realizes`: δ = 7/128, transferred to the routed 2 541-gate circuit on FakeTorino;
  - the `PhysGrade` row.

## 9. Work plan, implementation, risks

- **Revise §9 (the plan) into a record.** Phase 1 covered Stages 0–13c. Phase 2 covers Stages
  14–30, with milestones M3 (Stage 21) and M4 (Stage 23). M5 is the release.
  - The stage table, with each stage's scope and status, comes from `docs/PHASE2_ROADMAP.md`.
  - Stage 28 (device runs) was not run, by the author's decision of 2026-11-16. Stage 29 (the
    SQIR / VOQC comparison) was not run; see `docs/STAGE29_NOTE.md`.
- **Revise §9.5 (risks), outcome by risk:**
  - the pinned toolchain held, with no bump in Phase 2;
  - the kernel ceilings were measured and met by the compositional form;
  - the download risk was met by a separate pinned `.venv-hw`, approved once;
  - the reviewer-delegated process, from 2026-11-15, is recorded in DECISIONS.md.

## 10. Applications and future extensions

**Revise to the open list at M5** (from M5_REPORT):
- **Selection and proofs.** Count selection; clean ⇒ Cond(true); the dirty widening; the all-n
  forms of the 8n − 24 bound.
- **Device runs and noise.** Device runs (Stage 28, not run by the author's decision); randomized compiling in the certified path;
  idle noise in the bound; noise-aware routing beyond the pruned coupling map.
- **Structure and comparison.** "Circuit never imports Synthesis" as a stricter layering rule;
  the SQIR / VOQC comparison.

## 11. (new) Restoration under measurement (Track B; or an appendix)

This is the content of Paper 2's draft (`docs/notes/PAPER2_DRAFT.md`) at report length:
- `mbu_general`: MBU restores for any phase-exact compute block, and a compute phase stays as
  diag φ.
- Clifford ⇔ quadratic (`clifford_iff_quadratic`), and the IR boundary `mbu_exactly_quadratic`:
  `ifBit` wraps Clifford gates only, so j is existential.
- The restoration algebra:
  - `ancRestoreMix_of_kraus`;
  - `mbu_uncorrected`, the dephasing;
  - `AncRestore.widen`.
- The three regimes: dirty ⇒ Cond(cond) ⇒ Cond(true) ⇒ clean, with `reset_not_dirty`.
- Problem 1: `problem1_T_lower_bound` (8n − 24) under the stated cost model. Candidate B attains it
  for n = 6…12, with 8n − 20 at n = 4, 5.

## 12. (new) The hardware backend (Track C)

- **The target model** (24a):
  - `HardwareTarget` with capabilities, calibration snapshot and durations;
  - FakeTorino (mbu and coherent) and FakeWashington (coherent only);
  - the canonical-JSON snapshot hash.
- **Lowering and transpiling with a witness** (24b–25a):
  - the decomposition table;
  - SabreLayout as the only routing pass;
  - a witness that records the order;
  - the physical bound (25a).
- **The theorem chain:**
  1. `decomp_sound` and `translate_sound` (26a);
  2. `channelDenote_relabel`, `ud_swapEntry` and `channelDenote_embed` (26b1);
  3. `gateK_comm_of_disjoint` and `krausOps_reorder` (26b2);
  4. `applyWitness_sound` (26b3);
  5. the linear `applyWitnessQ` with `applyWitnessQ_ok` (26c1);
  6. `embed_zero`.
- **The per-instance checks**: fifteen committed check files, with reconstruction, edges, channel
  and start, closed by the kernel in 11–31 s.
- **The physical certificate**, `PhysGrade` and selection (26c2–26c2b).
- **The noise theorem and the conditional certificates** (27a–27b2):
  - the four premises stated in full;
  - the Pauli reading p = (d + 1)/d · r, with the clamp;
  - `phys_noisy_inst` for hw_n2 (δ' 0.1793) and hw_n3 (0.7521), and `gadget_noisy` (0.0995).
- **The frontier** (27c): n = 3 on FakeTorino and n = 2 on FakeWashington. The idle diagnostic
  shows (P-idle) as the premise furthest from a device.
- **What is not claimed:**
  - no device was run;
  - Qiskit is untrusted;
  - the bound is non-vacuous only for tiny instances on these calibrations.

## Errata and departures against v3, new in Phase 2

**Errata** are measured figures that differ. M5_REPORT §8 finds no new erratum beyond M3's two
kernel times (item 2 below). **Departures** are design choices that differ from v3, each with its
reason in PHASE2_SPEC (items 1, 3, 4).

To be appended to v3's list (items 1–16), after checking against v4:
1. **Departure, §9.3.1 / §10.1.1.** The second pattern is amplitude estimation, not amplification
   (§A.0); amplification is a corollary.
2. **Two kernel times** (`docs/M3_REPORT.md` §8):
   - Chapter 8's "kernel-checked in 7.2 s" is now 12.8 s of kernel time. The certificate gained
     the front-end block, `gradeExt_eq` and `hM_count` since v3.
   - Errata item 15's "6.4 s" for the second predicate is 13.0 s.

   The M5 values are in `docs/M5_REPORT.md`.
3. **Departure, §5.1.** The 14b ceiling is `grade_eq`, not `emitted_ok`, and is lifted by the
   cons-list scheduler state (18a).
4. **Departure, §3.3.3.** The perturbation bound δ_hw ≤ δ + G·p̄ is replaced by the conditional bound
   δ + Σ p_g + Σ r_j under (P-stoch), (P-ro) and (P-idle). For the running example it is 2.9
   (vacuous), as v3 anticipated.

Further items are for the author to add from v4.
