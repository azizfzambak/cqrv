# CQRV — Certified Quantum Realization

Implementation of *Applying Certified Quantum Realization: A Practical Implementation Guide*
(`docs/cqrv_report_revised_v3.docx`). The report is the specification; `docs/PLAN.md` is the
stage-by-stage execution plan; `CLAUDE.md` holds the rules every Claude Code session follows.

Status: **M3 reached (2026-11-15); Stage 21a complete (Stage 21a: the Count entry, Proposition 5.1 proved for the matcher, the QPLP record, `cqr certify --problem count`, certified selection); Stage 21b2: Theorem 3.3a exercised at `grover_pred_037` with `m = 5` — `search_unknown_M_8_32_5`, a library theorem over the two QPLP records with no committed certificate (PHASE2_SPEC §A.9 (12)); Stage 22a: the general MBU theorem `mbu_general` — any phase-exact compute block, measured in the X basis and corrected by a phase implementation of the same function, restores its ancilla, with `mbu_channel_correct` re-derived from it; Stage 22b: the Clifford corollary — the correction of MBU is Clifford iff the computed function has degree ≤ 2 over 𝔽₂ (`clifford_iff_quadratic`, `mbu_quadratic`); Stage 22c: the IR boundary — the IR admits only Clifford gates under `ifBit`, every IR Clifford gate is Clifford on the register, and a well-formed MBU circuit exists for `f` iff `f` is quadratic (`mbu_wf_forces_quadratic`, `mbu_exactly_quadratic`) (PHASE2_SPEC §B.1); Stage 23a: the restoration algebra, part one — block lists restore (`ancRestore_list`), restoration under measurement with a mixed data action (`ancRestoreMix_of_kraus`: MBU without its correction dephases, `mbu_uncorrected`), and ancilla reuse by widening (`AncRestore.widen`, `AncRestore.comp_widen`); Stage 23b: the three regimes — dirty (`AncRestoreDirty`, holding on every state by the span of the product states; the reset is never dirty, `reset_not_dirty`, so `mbuCircuit` is not), conditionally clean as a subspace regime (`AncRestoreCond`) with the exact hierarchy dirty = conditionally clean under `false` ⇒ conditionally clean ⇒ clean, both inclusions strict (`CZ(x0, anc 0)`), and the KG bridge `Inv.cond_value` in `CQRV/Grover/KGRegime.lean`; Stage 23c: the 8n − 24 counting argument as a theorem on KG Problem 1 schedules under a stated cost model (`problem1_T_lower_bound`, `CQRV/Synthesis/Problem1.lean`), candidate B attaining it for n = 6 … 12 with its emitted T-count equal to the model's cost (PHASE2_SPEC §B.2); Track C, Stage 24a: the hardware target model `HardwareTarget` (`docs/hardware_target.schema.json`), two targets extracted from Qiskit fake backends into `hw/targets/`, and `cqr hw capabilities` with the snapshot hash checked by Lean's SHA3-256; Stage 24b: the lowering of the canonical circuit JSON to Qiskit dynamic circuits (`hw/lower.py`), compared branch by branch on Aer against the statevector harness on 18 instances; Stage 24c: the weighted hardware bound δ_hw ≤ δ + Σ_types count · rate from a target's calibration snapshot, worst case over the device and exact in ℚ (`cqr hw bound`, `CQRV/Hardware/Bound.lean`; reported, not certified; vacuous on both fake backends) (PHASE2_SPEC §C.1), sorry-free (local CI)**; Phase 2 started (coherent uncomputation mode `--uncompute coherent` for `synthesize` and `certify`, Stages 15a–15b; a fourth certificate `examples/certs/grover_pred_037_coh`; the front end proved and stated in every certificate, Stages 16a–16b; the IR and grade extension — exact phase gates `p` / `cp` in the IR and both emitters, the second resource record `GradeExt` stated in every certificate as `gradeExt_eq` and recorded as `grade_ext`, schema 1.9.0 — Stages 17a–17b; `docs/PHASE2_ROADMAP.md`). Two Grover certificates, `grover_pred_037` and the
RevLib benchmark cone `simple_alu_x0_1` (and the few-ancilla variant `grover_pred_037_few`), are
`certified`: kernel-checked, axioms exactly `propext`, `Classical.choice`, `Quot.sound`, measured
grades, exact δ, the front end proved (`toNetwork_pred`; `front_end` kernel-checked in every `Cert.lean`, Stage 16b), and since Stage 14a the solution count M is
decided by the kernel for n ≤ 10 (`hM_count`; `--count-limit k`, default 10 since Stage 14c; larger n stay `certified
(conditional on: solution_count = M)`) (`examples/certs/`, with run reports). Since Stage 21a4, `cqr certify --budget w,d,t,a --prefer width|depth|t|anc` picks, among the three certified candidates (tree + mbu, tree + coherent, few:log + mbu), the one with the least key that fits the budget, and the certificate's theorem `selected` is kernel-checked against the candidates' builders (`examples/certs/grover_pred_037_sel`, schema 1.11.0). Acceptance is
the output of `scripts/ci_local.sh` (CI is not run remotely). Summary, open obligations, trust
boundaries and the report errata: `docs/M2_REPORT.md` (M2, frozen) and `docs/M3_REPORT.md` (M3: two
certified patterns, Proposition 5.1, certified selection; measured numbers with their sources).
Current state (Stages 0–21a, one page: machine-checked results, certificates, trust
boundaries, open items): `docs/PROJECT_STATUS.md`.

Layout: see CLAUDE.md. Obligations: `docs/SORRIES.md`. Decisions: `docs/DECISIONS.md`.

## Certifying a predicate

```bash
lake exe cqr certify examples/grover_pred_037.cqr --report
lake exe cqr certify examples/simple_alu_x0_1.cqr --solutions 30 --report   # M from the harness
lake exe cqr certify examples/grover_pred_037.cqr --profile illustrative_sc  # + declared budget
lake exe cqr certify examples/grover_pred_037.cqr --count-limit 0           # M as a hypothesis
lake exe cqr certify examples/grover_pred_037.cqr --problem count --precision 4      # counting certificate
lake exe cqr certify examples/grover_pred_037.cqr --budget 12,200,100,8 --prefer depth  # certified selection
scripts/ci_local.sh                                                         # local CI
```

## Building on Windows

Builds that compile Physlib (e.g. `lake build CQRVTests`) can exhaust memory on Windows when
Lake runs one Lean process per core, failing with `failed to read file '…olean': Invalid argument`.
Limit parallelism (Git Bash):

```bash
export LEAN_NUM_THREADS=4
lake exe cache get && lake build
```

Setting up a new workstation (repository and toolchain on an SSD, build, CI): `docs/SETUP_WORKSTATION.md`.

The hardware-study tools of Track C live in `hw/` and run in a separate git-ignored venv `.venv-hw`, pinned by `hw/requirements.lock` (`hw/README.md`); they are untrusted tools whose output Lean checks, and the test-harness `.venv` is unaffected by them.
