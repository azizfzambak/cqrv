# Response to the two reviews of the unified paper draft (draft 1) and the revision plan

Written 2026-11-16 by the reviewer session at the author's request. The two reviews are
`review_draft_1.docx` (Review A, about 10 300 words, section by section) and
`review_2_draft_1.docx` (Review B, about 3 500 words, claim calibration). Both concern
`CQRV_arXiv_Unified_Paper.pdf` (65 pages).

**Verification against primary sources.** Every point below was checked against the Lean sources,
the committed files, or a primary source before it was accepted or rejected. The Lean sources
checked include `CQRV/Circuit/IR.lean`, `CQRV/Grover/Reflections.lean`,
`CQRV/Hardware/Witness.lean`, `CQRV/DSL/Check.lean` and `CQRV/DSL/Eval.lean`.

The revised paper is `docs/notes/CQRV_ARXIV_PAPER_V2.md`, with its PDF on the author's desktop.

**Labels used below:**

| Label | Meaning |
|---|---|
| A | accepted; changed in the paper |
| P | accepted; needs project work (task R*, Section 4) |
| PA | partially accepted |
| R | rejected, with the reason |

---

## 1. Summary of the two reviews

**What both reviews find.**
- **The development.** Both find it substantial, and the arithmetic checked consistent (121/128,
  833/2048, ε ≈ 0.168426, δ ≈ 0.189431, Table 7, the 8n − 24 argument).
- **The weakness.** The weakness is *claim calibration*: places where the prose says more than the
  theorem.
- **Presentation.** The paper tries to be seven papers at once.
- **Evidence.** The evidence is mostly internal consistency, and the artifact is not public.

We agree with this diagnosis. The revision is a restructured and recalibrated paper, not a
copy-edit.

## 2. Point-by-point decisions

### 2.1 Mathematical and technical points

| # | Point (review) | Decision | What changes |
|---|---|---|---|
| 1 | "a rational approximation of a" (B1) | A | The estimate is sin²(πy/2^m), a real number indexed by the rational grid point y/2^m |
| 2 | "strict hierarchy" of regimes not established; Clean ⇒ Cond(true) is immediate (B2, A3.4) | A + P (R2) | "Strict hierarchy" is withdrawn. The paper states the implications, the separations that exist (dirty vs. clean, `reset_not_dirty`; the CZ instance), and that Cond(true) and Clean are mathematically equivalent, the converse being a missing formal factorization lemma. R2 proves it |
| 3 | "amplification is then a corollary" unsupported (B3) | A | Removed. Stated as a specification departure: estimation supplies count information and does not discharge the amplification pattern, which is not implemented |
| 4 | counting certificate "universal in M" misleading (B4) | A | Separated: the *parametric theorem* (`ae_parametric_lemma`) is uniform over networks and counts; the *generated certificate* concerns one network, and its ∀M quantifier is a formulation device equivalent to M = 32 |
| 5 | rotation / T-count accounting (B5) | A + P (R7) | Exact rules from `IR.lean` are now in the paper: `tCount` counts t, tdg and T-power `p a k` (2^k ∣ 8a, 2^k ∤ 4a); `cp` counts 0 in t; `rot` counts p / cp that are neither Clifford nor T-powers (`cp a k` with 2^k ∤ 2a). A per-block table for the counting certificate is added. The paper says that arbitrary-angle `cp` gates are native rotations whose Clifford+T synthesis cost is *not* in t. *One sub-claim of B5 is rejected:* controlled-S is **not** Clifford (CS is diagonal and in the third level of the Clifford hierarchy), so counting it in `rot` is correct |
| 6 | QIR floating-point angles are not linked to exact rotations (B6) | A + P (R6, optional) | Stated plainly: re-parsing validates gate structure and a numerical round trip, not exact equality with the IR rotation. R6 can add a proved bound through `diamondDist_ofUnitary_le` |
| 7 | the MBU proof sketch omits λ; the AND/MBU instance needs Z t in the compute block (B7, A3.1) | A | The proof sketch tracks λ (branch scalars 1/√2 and λ/√2). The corollary uses B′ = AND ++ [Z t], so that φ(a, b) = (−1)^{a∧b}. The `ComputesInto` notation is fixed (\|e_t(f(x))⟩, no stray Σψ) |
| 8 | no-cloning hypothesis \|X\| ≥ 2 (B8) versus its physical meaning (A1.5) | PA + P (R1) | Both reviews are right about different things. The linear-map statement holds for every non-empty X by scaling, and R1 adds it. The \|X\| ≥ 2 superposition statement is the one that survives restriction to normalized states, so it is kept and the paper explains the difference |
| 9 | "three-qubit frontier" overstated; rename it; δ′ < 1 is not usefulness (B9) | A | Renamed the *bound-vacuity frontier*, with the scope (family, iteration counts, two snapshots, modes, routings) in the sentence. A classical baseline table is added: a q-query classical search succeeds with probability (q+1)/N for M = 1. The certified 1 − δ′ beats it for hw_n2, the FakeWashington n = 2 instance and fr_n3 coherent, but **not** for hw_n3 or fr_n3 few:log |
| 10 | "works with whatever pass the vendor ships" (B10) | A | Replaced: the checker is independent of the routing *heuristics*, provided the output lies in the supported fragment (table translation, dependency-respecting reordering, layouts, SWAPs, conditioned blocks) |
| 11 | the conclusion lists too few assumptions (B11) | A | The conclusion and a new trust-model table (Section 3.6) enumerate the boundaries per certificate type |
| 12 | "measured grade" not true of every certificate (B12) | A | "a measured grade for flat certificates and a certified compositional upper bound for the counting certificate", everywhere |
| 13 | the title suggests a general compiler (B13) | A | New title and scope sentence: a two-pattern CQR prototype for Boolean predicates |
| 14 | matcher completeness is not semantic completeness (B14) | A | "signature-match completeness" throughout. A rejection is proved only relative to the extracted signature and the library |
| 15 | measured composition treats measurement and selection as free (B15, A1.3) | A | Called a *logical* measured-composition bound. The physical cost of measurement, classical computation, selection, re-preparation and latency is listed. Width max(w₁, w₂) at a measured interface relies on re-preparing the register |
| 16 | the unknown-count pipeline assumes M ≥ 1 (B16) | A + P (R8) | Stated as a precondition. R8 adds the M = 0 case: with no solution, G fixes \|s⟩, the phase outcome is 0, and the estimate is exact. It also adds a no-solution branch |
| 17 | surface language vs. loop-free core (B17, A1.1) | A + P (R9) | The paper now says that `evalProgram` returns the initial value on `loop` (a totality device). Theorem 4.2's premise `toNetwork prog = .ok net` excludes `loop`, so the theorem is about the loop-free core. Call inlining happens in the unverified surface checker, before the typed term. R9 separates the two languages formally |
| 18 | ideal initialization (and classical control) are implicit premises (B18) | A + P (R4) | Two premises are added: (P-prep), exact all-\|0⟩ preparation, and (P-ctrl), exact classical control and bookkeeping. R4 adds them to the manifests |
| 19 | RB numbers do not derive (P-stoch); coherent errors scale as √r (B19, A-weakness 2) | A | Emphasized: the result is a *conditional perturbation theorem parameterized by calibration-derived numbers*. For coherent errors the diamond distance can be of order √r, so the bound is optimistic unless the noise is twirled. Randomized compiling is named as the way to approach the premise |
| 20 | the emulator statistical protocol is incomplete; `emulator_validated` too strong (B20, A4) | A + P (R3) | The protocol is reported: α = 0.05, 4 000 shots, seed 25, one-sided Hoeffding margin √(ln(1/α)/(2·shots)) ≈ 0.0194, the success counts, and the comparison p̂ ≥ 1 − δ′ − margin. The status is renamed `emulator_sanity_checked` (R3) |
| 21 | artifact not accessible (B21) | P (R13, author) | Public repository, DOI, container: the author's publication decision. The proof hash should bind the CQRV source revision (R5) |
| 22 | measurements from different stages not comparable (B22) | A + P (R11) | Every performance table now names its stage and the checks enabled. Table 2 (the few:log timings) is labelled as measured at Stage 13a′, before the front-end block and the kernel-decided count were added. R11 re-measures all certificates at one commit |
| 23 | evidence is internal consistency; few benchmarks; no formal asymptotics (B23, A-weakness 1, A4.3) | A + P (R12) | Stated in the threats-to-validity section. "Linear" is described as the check's design (indexing by wire), measured to scale, not proved. R12 adds combinational benchmarks in the conditional / compositional regime |
| 24 | AI review is not independent validation (B24) | A + P (R14, author) | Said explicitly. A human expert audit of the main definitions is recommended (R14) |

### 2.2 Editorial points

| Point | Decision | What changes |
|---|---|---|
| Table 9 stars vs. "seven substantive" (B-ed1) | A | Nine items in seven groups (1, 2, 3–4, 5, 8–9, 12, 16), stated as such |
| Table 9 rows 3–4 malformed (B-ed2) | A | Rebuilt as two rows |
| "thirty stages" (B-ed3) | A | "Stage 0 and thirty further stages (31 in all)" |
| Wrong cross-reference 10.6 → 10.5 (B-ed4, A2) | A | Fixed (the numbering changes with the restructuring) |
| [Affiliation] placeholder (B-ed5) | P (author) | Left for the author |
| Unchecked references; phase-estimation placeholder (B-ed6, A4.1) | A | The placeholder is replaced by a comparison: QPE is mechanized for abstract unitaries in Qbricks and SQIR; Theorem 8.5 here is the two-eigenphase bound for the synthesized Grover iterate under the realization predicate. Remaining † marks name what the author must check |
| Line counts (B-ed7) | A | 39 114 lines of *library*; CLI and tests separately |
| 2 541 vs 4 170 gates (B-ed8) | A | Both stated with their roles |
| `RealizesExacts` (A) | A | "satisfies `RealizesExact`" |
| `ifBit` tensor order (A) | A | I ⊗ \|0⟩⟨0\|_j + gateU(g) ⊗ \|1⟩⟨1\|_j |
| Lemma 3.7's factor 2 (A) | A | Tracked |
| ε ≥ 0 not needed; `PseudoMetricSpace` assumptions; the triangle step with z_out (A1.2) | A | Added |
| Theorem 3.8's proof does not use pre-composition (A1.3) | A | Noted |
| H's table phase −1/8 and irPhase +1/8 worked out (A) | A | Added |
| Witness classical-bit map unexplained (A) | A + P (R15) | The map is parsed but not used. The reconstruction keeps the logical bit numbering, so any non-identity map makes `recon` fail (sound). R15 makes the check explicit |
| `diffU` sign (A2.2) | A | `diffU = 2\|s⟩⟨s\| − I`. The circuit implements its negative, and the sign is a branch scalar in Lemma 5.2, invisible on density operators |
| Counting tensor order and endianness (A3.2) | A | Stated |
| Why m = 5 in the composition; g₁ (A3.3) | A | At m = 4 the ε-ball contains outcomes with different iteration counts (composite δ ≈ 1.04, vacuous). At m = 5 every outcome in the ball gives r = 2 (`domain_8_32_5`), and g₁ = (21, 2862, 1364, 8) |
| The extractor's M versus the kernel's count (A1.4) | A | M is extracted symbolically for conjunctions of literals, or supplied (`--solutions`). For n ≤ 10 the CLI and the kernel decide the count, and a mismatch is a diagnostic |
| `prepare` algebra; "iteration bound 1"; Bool^{F₁} encoding; 0–1 BFS weights; p a k types (A) | A | Clarified briefly |
| Appendix A gaps (A) | A | Added `RealizesExact`, `applyWitnessQ_sound`, `phys_noisy_stochastic`, `mczFew_logDepth_ok`, `diffusionFew_logDepth_ancRestore`, and a note on `+` for ⊕ and `b` versus `bb` |
| Mark polarity; Phase 3 of schedule B; the three subcases in Theorem 7.3(b) (A2.3) | A | Clarified |
| Reference details (Aharonov et al. pages; Li et al. 2019 pages; Li et al. 2022 article number) | A | Added. The flagged accent in Chareton et al. is a rendering artifact of the PDF |
| Missing comparisons: Burgholzer–Raymond–Wille 2020 (Qiskit flow verification), QCEC, VOQC mapping, Li et al. 2026 (ancilla safety) (A-weakness 3, A4.2) | A | Added to related work and to a feature-comparison table. Burgholzer et al. (arXiv:2009.02376) and Li et al. (arXiv:2608.13099) were verified to exist. The VOQC routing-validation details could not be confirmed from primary sources and are marked † for the author |

### 2.3 Points rejected or corrected

| Point | Why |
|---|---|
| **A2.1:** the doubling interval should be [2^k − 1, 2^{k+1} − 1) | The review's model of a doubling step (unmark the marked indices, mark fresh ones to their right) is not KG §5.3's. In the implemented schedule a step's operations are (c − 1 − k, c + 2k + 1, c + 2k + 2). The trace for n = 8 (first account, Figure 3) gives the marks {1, 2} after one step and {2, 3, 4, 5} = [2, 6) after two, which is [k, k + 2^k). The closed form is the one proved in Lean. The paper now includes the n = 8 trace to prevent the confusion |
| **B5 (sub-claim):** "controlled-S rotations are Clifford" | False: CS is not in the Clifford group (it maps X ⊗ I to a non-Pauli). The `rot` count of 6 for the 4-qubit QFT is correct: all six controlled phases are non-Clifford |
| **Citation checker:** [Zambak 2026a, 2026b] "likely hallucinated" | These are the author's own *unpublished* technical reports (the specification of this project), which no search can find. They are now cited as "unpublished technical report, available from the author". The decision to release them with the artifact is the author's (R16). The checker's remark on the author's field is irrelevant to the paper |
| **A-weakness 1:** compositional blocks "when intermediate ancillae remain live across a single unrolled oracle cone" | The compositional form requires `liveEnd = 0` at block boundaries (Theorem 8.7's hypothesis), so a block cannot be cut inside a live cone. This is a real limitation for very large single oracles. It is stated, not solved |

## 3. The restructured paper

Review B's proposed structure is adopted.

**The new title.** *Certified Quantum Realization in Lean 4: A Two-Pattern Prototype with
Measurement-Based Uncomputation, Validated Routing, and Conditional Noise Bounds.*

**The main text:**
1. Introduction, with the scope and calibrated contributions.
2. Background, shortened.
3. Framework and trust model.
4. The certifying compiler.
5. Restoration under measurement: Lemma 6.3.2, general MBU, the Clifford boundary, the algebra and regimes, the two-ancilla diffusion, the 8n − 24 bound.
6. Certified patterns: Grover, counting, selection, the logical composition bound.
7. Validating routed circuits.
8. Conditional noise bounds.
9. Evaluation, with provenance and baselines.
10. Related work, with a comparison table.
11. Limitations and threats to validity.
12. Conclusion.

**The appendices:**
- A: Lean statements;
- B: reproduction and measurement provenance;
- C: specification errata;
- D: development methodology, moved from the main text and shortened;
- E: the stages.

The main text (Sections 1–12) shrinks from about 30 000 to about 17 000 words; with
references and appendices the paper is about 22 900 words, 46 pages
(`docs/notes/CQRV_ARXIV_PAPER_V2.md`; PDF `CQRV_arXiv_Paper_v2.pdf` on the author's desktop). The repeated hardware disclaimers
are replaced by the trust table and one fixed sentence.

## 4. Revision plan for the project (tasks R1–R16)

These tasks change code or committed files. R13, R14 and R16 are the author's.

**Status (2026-11-16).** R1, R2, R15: done (revision task A, `docs/tasks/REVA_TASK.md`; commits
6c66a87, 040e967, 8dfced6; accepted, CI 26 PASS / 4 n/a). R3, R4, R5, R10: done (revision task B,
`REVB_TASK.md`; commits f648115, d51a975, ba15d9c; accepted 2026-11-17, CI 26 PASS / 4 n/a). R12:
done (task C, `REVC_TASK.md`; commit ec06b84; accepted 2026-11-17, CI 26 PASS / 4 n/a): `addchk3`,
`wt8_3`, `wt8_3_count` certified; the comparator `cmp4` is harness evidence only (kernel peak above
8 GB). R11: task D (`REVD_TASK.md`). R6–R9 not scheduled.

| Task | Content | Size | Changes committed files? |
|---|---|---|---|
| R1 | `no_cloning_linear` for every non-empty X (scaling); keep the \|X\| ≥ 2 superposition theorem, documented as the normalized-state form | small | no |
| R2 | Clean ⇒ Cond(true), hence `ancRestoreCond_true_iff`, via a support-factorization lemma (a state supported on ℋ_D ⊗ \|0⟩ is ρ ⊗ \|0⟩⟨0\|) | small–medium | no |
| R3 | status `emulator_validated` → `emulator_sanity_checked`; the run protocol (α, shots, seed, counts, margin formula) in the manifests | small | manifests (schema bump) |
| R4 | premises (P-prep) and (P-ctrl) in every physical and conditional manifest | small | manifests (same bump as R3) |
| R5 | `proof_hash` binds the CQRV source revision (a tree hash of `CQRV/`, `Apps/`) | small | certificate JSON (schema bump) |
| R6 | optional: a proved emission-precision bound for floating-point rz angles (diamond distance ≤ 2·\|θ − θ̂\|·count) | small–medium | no |
| R7 | `cqr` prints and records the per-block T / rot accounting of compositional certificates | small | counting certificate JSON (field added) |
| R8 | counting at M = 0 (exact estimate 0, ε = δ = 0); a no-solution branch in "search after count" | medium | no |
| R9 | a loop-free core language with `toNetwork_pred` on the core; `loop` in the surface language only | medium | no |
| R10 | the `RealizesExact` / `AncRestore` statements of Appendix A, checked against Lean by a script | small | no |
| R11 | one benchmark run of every certificate at one commit (median of 5, enabled checks listed) | medium (time) | `certificate.json` timing fields |
| R12 | 2–3 combinational benchmarks (comparator, adder-based predicate, a larger RevLib function) in the conditional / compositional regime | medium | new certificates |
| R13 | public repository, immutable commit, DOI, container | author | — |
| R14 | a human expert audit of the main definitions (`Realizes`, `AncRestore`, `channelDenote`, the premises) | author | — |
| R15 | make the witness's classical-bit map an explicit identity check (or drop the field) | small | no (artifacts unchanged) |
| R16 | release or properly cite the specification report (v3 / v4) | author | — |

**Suggested order:** R1, R2, R15 (small proofs and checks), then R3–R5 (one schema bump), R7, R8,
R11, R12. The paper's text already states each item as its current truth: for example, "Cond(true)
⇔ Clean is mathematically immediate; its converse is not yet mechanized (R2)". Each task can then
update one sentence when it lands.
