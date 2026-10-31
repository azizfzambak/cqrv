# CQRV Phase 2 roadmap

Status: draft for the author's approval, 2026-10-29. Phase 1 (Stages 0–13c, plus Stage 14 in
progress) delivered the Grover vertical slice of report Chapter 8. Phase 2 answers the two
external reviews of the paper (originality, significance) and the hardware study, in the same
discipline: one stage = one task file = one buildable commit, stop conditions, ledger, decision
log, harness before proof.

## 0. Decisions that shape the plan (author, 2026-10-29)

| Decision | Choice | Consequence |
|---|---|---|
| Order of tracks | theory/originality first, hardware second | Stages 15–23 before 24–28 |
| Hardware access | none yet; start on a calibrated noisy simulator | Stage 28 (QPU runs) is gated on access |
| Publication | two papers | Paper 1: compiler + second pattern + hardware loop; Paper 2: restoration theory |
| External tools | Qiskit allowed as an *untrusted* tool | lowering produces a witness; Lean checks the witness; nothing certified depends on Qiskit |
| Code release | last | Stage 30 |
| Publication timing (revised 2026-10-29, late) | **nothing is published or put online before Stage 30** | the Zenodo (report v2 + v4) and arXiv (Paper 1) steps are deferred to Stage 30 and released together with the code, the data and the Phase 3 application's documentation; the paper is kept current at M3 and M5 but not posted; `docs/paper/ARXIV_CHECKLIST.md` is the checklist for that day |

Phase 2 goes beyond the report in three places: amplitude estimation instead of plain amplitude
amplification, the hardware backend, and the noise theorem. CLAUDE.md makes the report the
specification, so each of these gets a written specification **before** its first stage:
`docs/PHASE2_SPEC.md` (addendum v4 → v5 of the report, drafted by the reviewer, approved by the
author). Stages cite its sections the way Phase 1 stages cite report sections.

## 1. Goals, traced to the reviews

| Review item | Where it is answered |
|---|---|
| R1.1, R2.1: a second pattern that uses ε > 0, δ > 0, Theorem 3.3a and 3.3b | Track A: certified amplitude estimation / quantum counting (Stages 17–21) |
| R1.2, R2.2: a theorem about measurement-based uncomputation, not a gadget | Track B: restoration algebra (Stages 22–23), Paper 2 |
| R2.3: resource-aware certifying synthesis | Stage 21 (candidate selection under a budget, certified) and Stage 26 (physical grade) |
| R1.7, R2.4: source-level certification (`toNetwork`) | Stage 16 |
| R1.7: discharge M, extend the grade, formalize 8n − 24 | Stage 14 (M), Stage 17 (grade extension), Stage 23 (8n − 24 as a theorem about Problem 1) |
| R2.6: matcher completeness, decidable fragment | Stage 21 (report Proposition 5.1) |
| R1.5: quantify "specialization beats per-request verification" | Stage 29 (optional, decided at the M3 review) |
| R1.6, H.*: close the loop with reality; noise bound that is not vacuous | Track C: hardware (Stages 24–28) |
| R1.4: categorical identity of graded realizability | Track B optional (Stage 23b); Paper 2 |
| R1.7, R2.5, H.*: public artifact | Stage 30 |

Principles kept from Phase 1 and the hardware study: the Lean certificate stays a theorem about
the logical circuit; everything a kernel cannot check becomes a named hypothesis on the
certificate (as the solution count is today); a run on hardware is an experiment, never
"verified on hardware"; the physical grade with measurement cost, not the T-count, picks the
uncomputation mode on NISQ targets.

## 2. Stage plan

Sizes are Lean lines unless stated; Phase 1 estimates ran about 2× low, so each is given as a
range. "Gate" is the acceptance that ends the stage. Every stage keeps the repository sorry-free
and the committed certificates reproducible.

### Prerequisites

| Stage | Content | Report / spec | Size | Gate |
|---|---|---|---|---|
| 14a–c | solution count decided by the kernel for small n; profile `illustrative_sc`; kernel-time scaling study; 14c (added 2026-10-30): `--count-limit` default 10 and the `lean --tstack` experiment on the `decide +kernel` ceiling | §5.1.3, §8.2, §8.4, §9.5.1 | docs/tasks/STAGE14_TASK.md; 14a done 047a900 (2026-10-29); 14b done 4a591ef, accepted 2026-10-30: kernel time ≈ instructions^2.09, largest certified circuit 706 instructions (23.1 s), every n = 12 `hM_count` certificate timed out (carry_5, n = 10: 103 s, 11.4 GB), rand_a64's 1953-instruction literal hits the kernel's deep-recursion guard in `emitted_ok`; 14c done e4c254e, accepted 2026-10-30 (default 10 with the n = 11 negative test; `--tstack` 64 MB / 512 MB no effect) | three certificates without the M hypothesis; scaling tables; 14c: default 10, experiment recorded |
| 15a–b | **Coherent uncomputation mode** `--uncompute coherent` (15a: adjoint, mode, synthesizer, Lemma 6.3.2 coherent; 15b: `grover_parametric_lemma_gen`, certificates): each temporary AND undone by its adjoint (T ↔ T†, reversed), no measurement; `Circuit.adjoint` for measurement-free circuits (the IR has no adjoint today; `s`/`sdg`, `t`/`tdg` swap, list reversed) with `channelDenote_adjoint`; restoration lemma for the coherent oracle (the single-branch case of `ancRestore_of_kraus`); grade 8 T per AND; harness; `cqr certify --uncompute mbu|coherent` | §6.1.4, §10.1.1; PHASE2_SPEC §A.0.1 | 800–1 400 (15a actual: +874/−140 in 19 files) | `lemma_6_3_2_coherent`; both modes certified for the running example. **15a done 4087e48, accepted 2026-10-30**: mode as last defaulted argument, chain lemma generalized in place, Phase 1 statements unchanged; running example oracle (10, 41, 16, 2), D₈ (15, 59, 56, 7), Grover r = 2 (15, 200, 144, 7), 0 classical bits; new diagnostic `unsupported_combination` for Bennett / `few:` with `coherent`. **15b done d4cbdc7, accepted 2026-10-30**: `GroverData` and `grover_parametric_lemma_gen` (oracle abstract; `_diff` and every `GroverParams` statement are instances; no `hOn` hypothesis, none needed), `OracleCertCoh`, `grover_certificate_coherent` (tree MCZ certified from the circuit, no `DiffusionCert`), `cqr certify --uncompute`, schema 1.7.0 (`uncompute` written for coherent certificates only; explicit for all at Stage 17's 1.8.0), fourth certificate `examples/certs/grover_pred_037_coh` (15, 200, 144, 7), kernel 15.50 s, d 200 / 200 fits |
| 16a–b | **Front end proved** (docs/tasks/STAGE16_TASK.md, written 2026-10-30; **16a done 52ad73b, accepted 2026-10-30**: 1 280 lines, four build–fix rounds, `build_ok` + `build_succeeds` as two inductions so that `toNetwork_pred` needs no `hasLoop`): 16a `toNetwork_pred` (the network's predicate equals the evaluator on every input, under a decidable scoping predicate `tp.scoped`: `TExpr` variables carry names only), `toNetwork_WF`, `toNetwork_succeeds`; 16b every `Cert.lean` carries the typed-term literal `prog` with `prog_scoped`, `net_ok : toNetwork prog = .ok net` and `front_end : ∀ x, evalProgram prog x = Network.pred net n x` (kernel-checked), `cert` unchanged; the exhaustive 2^n validation becomes a regression test; schema 1.8.0 (third `front_end` wording, `uncompute` explicit everywhere). **16b done 7f46857, accepted 2026-10-31**: `CQRV/DSL/Render.lean` (`TypedProgram.renderLean`, an unverified printer now named in the trust boundary with parser and checker; round-trip test on every constructor), `prog`/`prog_scoped`/`net_ok`/`front_end` between `net` and `emitted` in all three templates, `cert`/`net`/`emitted` byte-identical (checked against 52ad73b), `certify` without `validateFrontEnd`, schema 1.8.0 tied to the wording both ways; kernel medians 14.40 / 16.70 / 12.60 / 25.40 s (machine regime, back-to-back old/new files equal; accepted as measured). Open item → Stage 17 review: a `Nat m` parameter makes the front-end block elaborate > 5 min (no corpus certificate has one) | §7.2–7.4, §5.3.3, §8.4.1 | 700–1 500 (`ToNetwork.build` ~50 lines over 11 `TExpr` constructors, `Eval.lean` 109 lines; `for` unrolling, `if` as a multiplexer and the `let`/environment invariant are the long cases) | a separate theorem `front_end` in every certificate (not inside `cert`); "validated" → "proved" in the trust report; parser, checker and literal printer remain the declared boundary |

Stage 15 comes first because both tracks need it: amplitude estimation uses the Grover iterate as
a controlled subroutine, and the report (§10.1.1) already notes that a state preparation containing
MBU has no adjoint; the hardware track needs it because mid-circuit measurement is the most
expensive operation on superconducting devices.

### Track A — certified amplitude estimation (quantum counting), Paper 1

The pattern: for a predicate P with M solutions among N = 2^n, estimate a = M/N. The circuit is
quantum phase estimation on the Grover iterate G with m phase qubits: H on the phase register,
controlled-G^{2^k} from phase qubit k, inverse QFT, measurement of the phase register, decoding
y ↦ ã = sin²(π y / 2^m). The classical theorem (Brassard–Høyer–Mosca–Tapp 2002): with probability
at least 8/π², |ã − a| ≤ 2π √(a(1−a)) / 2^m + π² / 4^m. This is an (ε, δ)-realization with both
parameters non-zero, under a metric on the output; the solution count M = N·a is obtained, not
supplied. Controlled-G needs no new gates: controlled-O_P is the phase oracle of the network
c ∧ P (one more input), and the controlled diffusion is H X (MCZ on n+1 qubits) X H, so
Lemma 6.3.2 and the synthesizer are reused as they are. The inverse QFT needs phase gates, which
is the one IR extension.

| Stage | Content | Spec | Size | Gate |
|---|---|---|---|---|
| 17 | **IR and grade extension**: exact phase gates `p k` = diag(1, e^{2πi/2^k}) and controlled `cp k`; semantics, WF, scheduler, emitters (`p`/`cp` in OpenQASM 3 with the evaluated power `2^k`; in QIR `p` as `rz` with a hex-float angle and `cp` as its five-gate decomposition `decomposeCp`, `decomposeCp_unitary`), harness; a second record `GradeExt` (two-qubit gate count, T-depth, rotation count, measurement count, feed-forward count) computed by the same scheduler and stated in every certificate (`gradeExt_eq`); `Grade` and all existing statements unchanged. **Ceiling to respect (14b):** `decide +kernel` on the emitted literal failed at 1953 instructions (kernel deep recursion; 14c, 2026-10-30: `lean --tstack` 64 MB and 512 MB did not move the failure point, so the ceiling is not lifted from the command line in this toolchain); the Stage 19–20b counting circuits must stay below ~1953 emitted instructions or the equality proof form changes (chunked `emitted` literal, equality in pieces) — **decided at the 17b review (2026-10-31): the chunked literal is designed and tried at Stage 18, on the small QFT / AQFT circuits (the first circuits built from `p` / `cp` and the first new circuit family with a kernel-decided equality), before Stage 19 produces the counting circuits that approach the ceiling.** **Split 17a / 17b (docs/tasks/STAGE17_TASK.md, written 2026-10-31; §A.1 amended the same day: T-power rule as a divisibility condition, QASM angle with the evaluated power, QIR hex float, `cp` under `ifBit` refused by the QIR emitter, `emit-sample` test path):** 17a IR, semantics, WF, scheduler, `GradeExt`, `decomposeCp` (library only); 17b emitters, re-parsers, harness, `gradeExt_eq`, schema 1.9.0, the four certificates regenerated. **17a done b32b999, accepted 2026-10-31** (CI 16 PASS): 939 insertions, all theorems proved, nothing tracked, no existing statement changed (checked by script), golden circuits and certificates byte-identical; two accepted deviations from the task text — `decomposeCp_gate` needs `t.inRange` besides `c ≠ t` (false without it: an out-of-range qubit reads 0) and `decomposeCp_unitary` needs no `isUnitary` hypothesis (its hypothesis is `Gate.cpOk`: distinct operands, target in range, for every top-level `cp`); measured `GradeExt` (twoQ, tDepth, rot, meas, ff): grover (126, 39, 0, 18, 36), alu (137, 28, 0, 15, 30), few (106, 77, 0, 8, 16), coh (216, 74, 0, 0, 0). 17b additionally: `decomposeCp_unitary_wf` on a WF circuit's own register; watch the kernel cost of `tDepth` (depth × gates; the 30 s stop condition of the task text, fallback: deduplicated T-layer indices). **17b done 9fc909b, accepted 2026-10-31** (CI 16 PASS): 43 files, +896/−193; OpenQASM `p(2*pi*a/N)` / `cp(…)` with the evaluated power, QIR `rz` with the hex-float angle (`qirAngle`, π as the bits of `math.pi`) and the five-gate `decomposeCp` (`decomposeCp_unitary_wf` proved, standard axioms), the `rz` declaration only when used so every committed `.qir` stayed byte-identical, `cp` under `ifBit` refused (`emit` / `unsupported_in_qir`, nothing written); `decomposeCp` moved to `CQRV/Circuit/IR.lean` (the emitters do not import the semantics); `Emit.sampleCircuit` + `CertifyTool emit-sample` as the test path; `gradeExt_eq` in every `Cert.lean`, `grade_ext` under schema 1.9.0 with nine negative tests, certify_check consistency and byte-identity (16b files + exactly the theorem); kernel medians 16b → 17b 14.40 → 18.10, 16.70 → 16.90, 12.60 → 15.40, 25.40 → 33.50 s, `gradeExt_eq` alone 9.26 / 7.03 / 7.95 / 17.5 s under the certificate's metric (the reviewer's reading of the 30 s rule; the profiler's per-declaration figure double-counts the `decide +kernel` evaluation) — the `tDepth` definition stays. **Stage 17 complete.** **Open item from 16b (2026-10-31):** a `Nat m` parameter makes the `Cert.lean` front-end block elaborate for more than five minutes where `Vec`-only programs take seconds (cause not isolated; no corpus or committed certificate has one) — decided at the 17b review (2026-10-31): a time-boxed diagnosis (30 minutes, `set_option profiler true` on a scratch program with a `Nat m` parameter, report which declaration is slow and why, no fix) as step A0 of the Stage 18 task text | PHASE2_SPEC §A.1 | 500–900 | existing certificates byte-identical except the new `gradeExt_eq` line; `tests/diff/statevector.py` extended to `p`/`cp` (it is a pure-state simulator with a fixed gate table) |
| 18 | **QFT and approximate QFT**: circuits `qft m`, `aqft m kmax`; `qft_unitary` (the circuit's unitary is the DFT on Fin (2^m)); `diamondDist_unitary_le` (diamond distance of two unitary channels ≤ 2·‖U − V‖); `aqft_diamond_le` (dropping rotations with k > kmax costs at most Σ dropped angles, Coppersmith/Barenco et al.) | PHASE2_SPEC §A.2 | 800–1 500 | both theorems; harness on m ≤ 6 |
| 19 | **Counting circuit**: `controlledGrover P n` from the networks c ∧ P and all_{n+1}; `powers` by concatenation; `countingCircuit n m P` (phase register, controlled powers, inverse (A)QFT, measurement); `AncRestore` of the whole from the existing `AncRestore.comp` / `ancRestore_foldl` over `Circuit.append`; harness: phase-register statistics against the closed form for n ≤ 6, m ≤ 4 | PHASE2_SPEC §A.3 | 600–1 000 | restoration theorem for `countingCircuit`; harness agreement |
| 20a | **QPE lemma**: eigenvectors ψ_g ± iψ_b of G in span{ψ_g, ψ_b} with eigenvalues e^{±2iθ} (from `reflection_geometry` and `iteration_induction`); `ketS` as their superposition; the two-eigenphase QPE bound: Pr[|y/2^m − θ/π| ≤ 1/2^m mod 1] ≥ 8/π² (the geometric-sum estimate, proved once) | PHASE2_SPEC §A.4 | 1 500–3 000; the hardest proof of Phase 2 | `qpe_two_phase_bound` sorry-free |
| 20b | **Amplitude-estimation parametric lemma**: `Realizes (CountSpec P) (decodeAE m) (countingChannel …) ε δ (grade)` with ε = 2π√(a(1−a))/2^m + π²/4^m and δ = 1 − 8/π², exact decoding POVM over Fin (2^m) relabeled to ℚ; the AQFT variant by Theorem 3.3b (`coherent_composition_diamond` with η from Stage 18): the first certificate in which the diamond distance appears | PHASE2_SPEC §A.4 | 800–1 500 | `ae_parametric_lemma`, `ae_parametric_lemma_aqft`; kernel-checked certificate for n = 8, m = 4 |
| 21 | **Second library entry and decidability**: problem class `Count` in the DSL request (`cqr certify --problem count`), extractor, QPLP entry φ_Count with its precondition, the QPLP record of report §3.2 instantiated at last (`CQRV/Patterns/Basic.lean` is a placeholder today) with two entries, `library := [groverEntry, countEntry]`, `groverInstance` generalized (it rejects every entry but "Grover"), repair hints across entries, certificate generator and status words for (ε, δ); **Proposition 5.1**: matching is decidable and the match set is empty or a singleton for the Miller fragment, i.e. completeness of the matcher on the fragment (a rejection is a proved non-match); **certified selection**: under `--budget`, the tool builds the admissible candidates (diffusion shape × uncomputation mode × m), computes their grades, and the certificate states the chosen candidate and the criterion; if the candidate space is finite and enumerated, the certificate states that no admissible candidate is better in the chosen order | §4.2.1, §9.3.2; PHASE2_SPEC §A.5–A.6 | 1 000–1 800 | **Milestone M3**: two patterns certified end to end; Prop. 5.1 proved; selection certificate |
| 21b (stretch) | Measured composition exercised: counting followed by search with the estimated M (Theorem 3.3a with its domain and non-expansiveness hypotheses on the metric ã ↦ N·ã); if the classical post-processing stage cannot be expressed as a graded channel cheaply, record the obstacle and exercise 3.3a on two toy stages, as the report's own validation gate did for 3.3b | PHASE2_SPEC §A.7 | 400–1 000 | or a documented obstacle |

### Track B — a theory of restoration under measurement, Paper 2

| Stage | Content | Spec | Size | Gate |
|---|---|---|---|---|
| 22 | **General MBU theorem**: if a measurement-free block computes a Boolean function f of the data's computational basis into a clean ancilla (as a basis-state function, with the relative-phase convention of the temporary AND), then "measure the ancilla in the X basis; on outcome 1 apply the phase oracle O_f to the data" restores the ancilla and applies the identity (`mbu_general`); the temporary logical-AND is the instance f = a ∧ b with O_f = CZ; corollary: the correction is Clifford iff f has algebraic degree ≤ 2, which explains why MBU is free for ANDs and costly beyond | PHASE2_SPEC §B.1 | 800–1 500 | `mbu_general`; the AND/MBU lemma re-derived from it |
| 23 | **Restoration algebra**: sequential (exists), parallel (disjoint registers), conditioning on a classical bit, ancilla reuse across certified blocks, and "local restoration implies global restoration" for a block structure; the three regimes of report §6.2: clean (`AncRestore`), dirty (`AncRestoreDirty`: identity on every ancilla state), conditionally clean (the KG invariant as an instance); the 8n − 24 counting argument as a theorem about Problem 1 schedules (`problem1_T_lower_bound`) | §6.2, §6.3; PHASE2_SPEC §B.2 | 1 200–2 500 | the three regimes with composition laws; Paper 2 draft |
| 23b (optional) | Unqomp/Silq safety conditions imply the Stage 22 criterion (paper-level argument, partial mechanization); graded realizability as a fibration over the grade monoid with Theorems 3.3a/b as composition laws; the obstruction theorem as "no copy-preserving monoidal functor into CPM(FdHilb)" | §3.1, §2.1 | open | decided at the M3 review |

### Track C — hardware backend, simulator first, Paper 1

Architecture (from the hardware study): the Lean certificate is unchanged; the backend is a new
layer after it; untrusted tools do the work and produce a witness; Lean checks the witness; the
rest becomes named hypotheses. The backend is built around dynamic-circuit semantics from the
start, because every MBU is a mid-circuit measurement with feed-forward.

| Stage | Content | Spec | Size | Gate |
|---|---|---|---|---|
| 24 | **Target model and lowering**: Python package `hw/` with pinned Qiskit, Aer and the runtime fake provider (this supersedes the Phase 1 rule "no Qiskit", DECISIONS.md 2026-10-26, by the author's decision of 2026-10-29: Qiskit is an untrusted tool whose output Lean re-checks); `HardwareTarget` JSON (native gates, coupling map, capability flags: mid-circuit measurement, feed-forward, reset; durations; calibration snapshot: 1Q/2Q/readout/mid-circuit errors, T1/T2), hashed and timestamped, from a fake backend or `AerSimulator.from_backend`; `cqr hw capabilities`; lowering of the canonical circuit JSON (not the QASM text) to a Qiskit dynamic circuit with `if_test` blocks; ideal Aer simulation compared branch by branch with the Lean/Python reference for n ≤ 6; `Profile.pBar` (one rate) replaced by per-operation-type rates from the snapshot, and the bound δ + Σ_i η_i weighted per operation | PHASE2_SPEC §C.1 | Python 800–1 500; Lean 100–200 | `if_test` confirmed on Aer; lowering equals the reference on all branches; weighted bound reported |
| 25 | **Transpile with a witness, noisy simulation, run reports**: seeded Qiskit transpile against the target; witness = initial layout, SWAP insertions with positions, decomposition-table entries per gate, final layout and bit mapping; `PhysicalArtifact` manifest hash-linked to the certificate; `cqr hw run --sim` on the snapshot noise model; run report with job data, counts, success frequency p̂ = #{x : P(x)} / shots, binomial confidence interval and the one-sided test p̂ ≥ 1 − δ_hw − Hoeffding margin; progressive instances (AND/MBU gadget, n = 2, 3 Grover, the committed examples, both uncomputation modes) | PHASE2_SPEC §C.2 | Python 800–1 500 | reports for all instances; ideal vs. noisy vs. reference table |
| 26 | **Witness checking in Lean and the physical grade**: decomposition table with one proof per entry (`decomp_sound`: the native list equals the logical gate up to global phase); `applyWitness : Circuit → Witness → PhysCircuit`; `applyWitness_sound` (the physical channel is the logical channel followed by a permutation of the register, so `Realizes` and `AncRestore` transfer with the decoding POVM permuted); kernel checks that every two-qubit gate lands on a coupling edge and that the reconstruction equals the tool's output literally; `PhysGrade` (physical qubits, wall-clock depth from durations and feed-forward latency, two-qubit count, mid-circuit measurements, feed-forward count) by the ASAP scheduler with a timing model; status words `logical_certified`, `hardware_compatible`, `physical_translation_validated`, `emulator_validated`; the physical grade, not the T-count, selects the uncomputation mode per target | PHASE2_SPEC §C.3 | 1 200–2 000 | physical certificate for the running example on a fake IBM target |
| 27 | **Noise theorem**: `noisy_realization`: if the ideal physical circuit (ε, δ)-realizes S and operation i's noisy implementation is within η_i of its ideal in the diamond distance, the noisy composite (ε, δ + ½ Σ η_i)-realizes S; needs `diamondDist_tensor_id` (stability under tensoring with the identity on the rest of the register, the property cited in Phase 1) or, as fallback, η_i stated on the full register; conditional hardware certificate "certified (conditional on: solution_count; calibration snapshot h; per-operation diamond bounds η)"; randomized compiling in the lowering so that the stochastic-noise premise is approximately true; feasibility frontier per target: the largest (n, r, #ANDs, mode) with Σ η_i < 1 − δ | §2.3.2, §6.6; PHASE2_SPEC §C.4 | 800–1 500 | `noisy_realization`; frontier table; a non-vacuous certificate for a small instance on a real calibration snapshot |
| 28 (gated) | **QPU runs**, when access exists: trapped-ion first (no routing, native mid-circuit measurement), IBM second (routing witness, measurement cost); calibration-hashed run reports; measured vs. certified comparison; the paper's "closing the loop" section | PHASE2_SPEC §C.5 | Python | experiment report; never the word "verified on hardware" |

### Closing

| Stage | Content | Gate |
|---|---|---|
| 29 (optional) | quantify the thesis: the same circuit verified from scratch in SQIR/VQO (proof size, effort, check time) against CQR's specialization; decided at the M3 review | comparison table or a documented reason not to |
| 30 | artifact release (Zenodo DOI + public repository with the CI run elsewhere), report v5 (PHASE2_SPEC merged), Paper 1 revision, Paper 2 submission | **Milestone M5** |

Housekeeping with the first Phase 2 stage: `docs/PLAN.md` (Phase 1, stages 0–9) is superseded by this file for Phase 2; `PROJECT_STATUS.md` gets a Phase 2 section; `README.md` status line.

## 3. Order and milestones

```
14a 14b │ 15a 15b 16 │ 17 18 19 20a 20b 21 (21b) │ 22 23 (23b) │ 24 25 26 27 (28) │ (29) 30
 prereq │ both  │        Track A, Paper 1      │  Track B, P2 │   Track C, Paper 1  │ close
                                           M3 ─┘           M4 ┘                  M5 ┘
```

- **M3** (after Stage 21): two patterns certified end to end, Prop. 5.1 proved, certified
  selection. Review: decide 21b, 23b, 29; revise Paper 1's claims.
- **M4** (after Stage 23): Paper 2 draft.
- **M5** (after Stage 30): release and submissions.

Track B does not depend on Track A beyond Stage 15 and can be moved before Track A if the
amplitude-estimation proofs (Stage 20a) stall; that is the planned fallback for a stalled 20a,
together with a per-instance kernel evaluation of the counting statistics for the committed
example (the same move Phase 1 made for the two-ancilla MCZ before its every-n proof).

## 4. Risks and stop conditions specific to Phase 2

| Risk | Signal | Response |
|---|---|---|
| QPE bound (20a) exceeds its range | 3 rounds without closing the geometric-sum lemma | fall back to the per-instance kernel evaluation; move to Track B; return after M4 |
| IR extension breaks existing statements | any Phase 1 theorem must change | stop; the new gates must be additive (new constructors with the identity outside WF) |
| `diamondDist_tensor_id` unprovable with Physlib's primitives | no proof route after 2 rounds | state η on the full register (documented weaker hypothesis) |
| Aer lacks a needed dynamic-circuit feature | `if_test` or reset unsupported | stop; report; consider pytket/Quantinuum emulator as the first target |
| Qiskit version drift | lock file differs from the run | pinned `hw/requirements.lock`; CI step compares |
| Scope creep in Track C | a stage wants to verify the transpiler | witness checking only, by design |

## 5. What each paper will claim after Phase 2

Paper 1 (revision): a certifying compiler with two patterns (search, counting) whose certificates
state (ε, δ, grade) triples, including the first kernel-checked certificate for an approximate
quantum algorithm with a synthesized oracle inside it and a diamond-distance bound in its proof;
source-level certification from the DSL; a hardware backend whose physical artifact is linked to
the logical certificate by a checked witness, a noise theorem with a feasibility frontier on real
calibration data, and simulator (and, when available, QPU) runs compared with the certified
probabilities.

Paper 2: a semantic theory of ancilla restoration under measurement-based uncomputation on
density operators: the general MBU theorem, the restoration algebra for the three ancilla regimes,
the Clifford-correction characterization, and the Problem-1 T-count bound; related to the
language-level safety conditions of Unqomp and Silq.

Revision items for Paper 1 accumulated during Phase 2 (fix at the revision, not piecemeal):
- Stage 14a: the profile is `illustrative_sc` (the paper says `ibm_kyiv` in introduction.tex,
  certificates.tex, evaluation.tex, appendix.tex); the committed certificates no longer take the
  M hypothesis for n ≤ 12 (`hM_count`, status `certified`), so the "conditional on M" wording and
  the trust-boundary table change; certificate schema 1.6.0 with `solution_count`.
- Stage 14b: kernel-time figures: the paper's recorded medians (12.30 / 11.10 / 6.72 s, from the
  bimodal 14a run) against KERNEL_TIMES.md's 8.02 / 8.89 / 6.80 s (unimodal run); one scaling
  paragraph from SCALING.md (kernel time ≈ instructions^2.09, circuit-only 2.06; largest certified
  circuit 706 instructions, 23.1 s; the kernel-decided count memory- and time-bound at n = 12 on a
  16 GB machine; the `decide +kernel` deep-recursion ceiling at 1953 instructions, with 14c's
  stack result); state the `--count-limit` default as it stands at the revision (10 after 14c).

## 6. Phase 3 target: the three-verdict application (author, 2026-10-29)

The author's end goal, stated after the Phase 2 plan was approved: an application that (1) loads a
classical algorithm or program, (2) loads the specification of the quantum hardware at hand,
(3) returns one of three verdicts: **not adaptable** to that quantum computer; **adaptable after
changes** to the program that keep the same output; **adaptable as is**; and (4) for verdicts 2–3
runs the pipeline and produces the output (certificate, circuit, run report, simulator or device
run). Phase 3 is that application. Phase 2 does not build it, but every Phase 2 interface decision
below is made so that Phase 3 is a layer over the CLI, not a rewrite.

### 6.1 What the pipeline can honestly decide

| Verdict | Pipeline event | Honest wording in the application |
|---|---|---|
| 1 not adaptable | no library pattern matches (Chapter 4 matcher fails, repair hints empty), **or** the matched pattern's grade exceeds the hardware budget (budget order §3.1, `HardwareTarget`, Stage 24), **or** the noise bound (`noisy_realization`, Stage 27) leaves a success probability below the requested threshold | "no pattern in this library applies to this specification on this hardware", with the failing side named (library / budget / noise). Never "no quantum algorithm exists": every classical program has a reversible embedding, and absolute non-existence is not provable in general |
| 2 adaptable with changes, same output | a match after anti-unification (`lgg`, repair hints: which sub-term to change and how), **or** a match only under the (ε, δ) relaxation | the output is probabilistic: for checkable outputs (search) the application offers exactness by verify-and-repeat, expected repetitions 1/(1 − δ); for estimates (counting) "the same output within ε with probability ≥ 1 − δ" |
| 3 adaptable as is | match, certificate sorry-free and axiom-audited, grade within budget; status `certified` | the current `certified` status line, plus the hardware feasibility line |

Input scope: a DSL (Chapter 7) kernel, i.e. the decision / counting / optimisation part of the
program. A front end from a restricted subset of a general language (Python or C functions over
fixed-width integers and Booleans, loop-free or bounded loops) into the DSL is Phase 3 work;
arbitrary programs (unbounded loops, pointers, I/O) are out of scope and the application must say
so at load time (a fourth, pre-verdict outcome: "not expressible").

### 6.2 What Phase 3 adds (not scheduled; sized after M5)

| Item | Content | Builds on | Relative cost |
|---|---|---|---|
| P3.1 library breadth | 3–4 further patterns, each with a QPLP record, parametric lemma and certificate template: Dürr–Høyer minimum finding (on the Grover iterate), amplitude amplification with a user-supplied checker, Simon / period finding (function oracles: a new oracle class and synthesis path), quantum-walk search if time allows. Excluded: HHL-class patterns (block encodings; certification cost out of reach), QAOA / VQE (no output guarantee; at most a "heuristic, uncertified" label outside the three verdicts) | Track A (the second pattern is the template), Stage 21 library interface | largest: Track A is one pattern and takes five stages |
| P3.2 front end | extractor from the restricted language subset into the DSL, with the source hash in the certificate; Stage 16's `toNetwork_pred` is the trust anchor | Stage 16 | medium |
| P3.3 verdict engine | one JSON verdict record per run: verdict, pattern, repair hints, (ε, δ), grade, budget check per component, noise bound, expected repetitions; every terminating diagnostic of the CLI maps to exactly one verdict | Stage 21 certified selection (§A.6), Stages 26–27 `PhysGrade` and feasibility frontier | small |
| P3.4 user interface | thin web or desktop layer over the CLI and the verdict record; device runs through Track C | Stages 24–28 | smallest; last |

### 6.3 Constraints this target puts on Phase 2

- From Stage 21 on, status words and repair hints are emitted as machine-readable JSON
  (`cqr match --json`, `cqr certify` JSON), not only as text.
- The QPLP library interface stays pattern-agnostic (no Grover-specific field in the record or
  in `library`); Stage 21 enforces this when the second entry lands.
- `HardwareTarget` (Stage 24) is designed as a user-supplied file: schema, validation
  diagnostics, and a documented minimal set of fields.
- Each diagnostic that ends a run is classified in its DECISIONS entry as verdict 1, 2 or "not
  expressible"; no diagnostic is left unclassified.

A Phase 3 roadmap is written after M5, in the same form as this file.
