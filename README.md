# CQRV — Certified Quantum Realization

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24302653.svg)](https://doi.org/10.5281/zenodo.24302653)

A certifying compiler from a small classical specification language to quantum circuits, with Lean 4
certificates. It implements the technical report *Applying Certified Quantum Realization: A Practical
Implementation Guide* (`docs/cqrv_report_revised_v3.docx` with its errata; the report is the
specification). A request — a Boolean predicate over `n` bits, a search or counting problem — is
matched against a library of proof-carrying patterns, instantiated, synthesized into a circuit with
measurement-based or coherent uncomputation, and emitted as QIR / OpenQASM 3; the output is a
self-contained Lean file whose theorem the kernel checks: the circuit realizes the specification with
an exact failure bound δ and a measured resource grade (width, depth, T-count, ancillae), and
restores its ancillae. Track C extends the chain to a hardware description: the circuit routed on a
Qiskit fake backend is checked against the certified one, and the noise statement is a theorem
conditional on four named premises. **Nothing is "verified on hardware"**: no device was run.

Phase 2 is complete (Stages 14–30a; milestone M5 ready, 2026-11-16). The measured state of the
project, with every number's source, is `docs/M5_REPORT.md`; reproduction and the trust boundary are
`docs/RELEASE.md`; the earlier milestone reports are `docs/M2_REPORT.md` and `docs/M3_REPORT.md`
(frozen). The stage-by-stage history is `docs/PROJECT_STATUS.md` and `docs/DECISIONS.md`.

**Release v1.0.0 (November 2026).** Everything up to Phase 3 is described in one paper,
`paper/Zambak_2026_CQRV.pdf` (source `paper/Zambak_2026_CQRV.md`, build `paper/tools/build.ps1`),
published as a preprint on Zenodo (https://doi.org/10.5281/zenodo.24302653). The code the paper describes is commit `2f8200b`; the tag `v1.0.0`
adds only documentation (license, citation file, release notes, the paper).

## The three tracks

**Track A — the certifying compiler.** Two patterns, Grover search and quantum counting (amplitude
estimation with an exact or approximate inverse QFT), each a parametric lemma in the library;
`cqr certify` specializes the lemma to a request and the kernel decides the instance facts — the front
end's translation, the synthesizer's output, the solution count, the exact δ, the grade. The matcher
is proved sound and complete for its fragment (Miller patterns with uniform arity), and selection
under a resource budget is certified. Six logical certificates for the worked predicates
(`examples/certs/grover_pred_037*`, `simple_alu_x0_1`) plus five for the hardware instances
(`hw_n2`, `hw_n3`, `fr_*`); kernel times 0.3–25 s each.

**Track B — restoration under measurement.** The mathematics of measurement-based uncomputation
(MBU): any phase-exact compute block, measured in the X basis and corrected by a phase implementation
of the same function, restores its ancilla (`mbu_general`); the correction is Clifford iff the
function is quadratic over 𝔽₂, and the IR admits exactly those (`clifford_iff_quadratic`,
`mbu_exactly_quadratic`); the restoration algebra (block lists, mixed data actions, ancilla reuse by
widening) and the three regimes dirty ⇒ conditionally clean ⇒ clean with a strict hierarchy; and the
8n − 24 bound on Khattar–Gidney Problem 1 schedules under a stated cost model, attained by the
few-ancilla construction for n = 6 … 12 (`problem1_T_lower_bound`).

**Track C — the hardware chain, on fake backends.** A hardware target (basis gates, coupling map,
capabilities, calibration snapshot, durations) is read from a Qiskit fake backend; our basis
translation is proved sound; Qiskit's layout and routing is untrusted and produces a witness, which
Lean reconstructs and proves sound (`applyWitness_sound`); every committed artifact has a
kernel-checked `Check.lean`; the physical certificate transfers the realization to the routed circuit
from all-|0⟩ (`phys_realizes`) with an exact physical grade; the noise theorem on a step semantics
with the classical register gives the conditional certificate (`phys_noisy_inst`): under (P-cal),
(P-stoch), (P-ro), (P-idle), for every choice of the arbitrary error channels, the noisy physical
channel realizes the specification with an exact δ'. The feasibility frontier
(`docs/hw_frontier/FRONTIER.md`) shows the bound is below 1 only up to n = 3 ANDs on FakeTorino and
n = 2 on FakeWashington on the shipped calibrations; the emulator runs (`docs/hw_runs/`) agree with
the non-vacuous bounds as a sanity check.

## Building and checking

```bash
export LEAN_NUM_THREADS=4                  # Windows: one Lean per core exhausts memory
lake exe cache get && lake build           # library, tests, the cqr executable
lake exe cqr certify examples/grover_pred_037.cqr --report       # a certificate, with its run report
lake env lean examples/certs/grover_pred_037/Cert.lean           # check it yourself: #print axioms
scripts/ci_local.sh                        # the 26 local CI steps (pass mark 26 PASS, 0 FAIL, 4 n/a)
```

The Python test harness lives in `.venv` (`tests/diff/requirements.lock`); the hardware tools of
Track C in a separate git-ignored `.venv-hw` (`hw/requirements.lock`: qiskit 2.6.2, qiskit-aer 0.18.2,
qiskit-ibm-runtime 0.52.1, offline fake backends only; `hw/README.md`). Setting up a workstation:
`docs/SETUP_WORKSTATION.md`. Toolchain and dependency pins: `lean-toolchain`, `lake-manifest.json`
(never bumped ad hoc).

## Where to look

- `docs/RELEASE.md` — reproduction (pins, venvs, every CI step with its command and time, what
  reproduces byte for byte) and the trust boundary (kernel-checked / untrusted / premise).
- `docs/M5_REPORT.md` — what is certified, with axiom lines; the committed certificates with grades,
  `PhysGrade`, δ and δ', kernel times; the CI; the open items; the claims the papers may make and
  must not make.
- `docs/STAGE29_NOTE.md` — why the SQIR / VOQC comparison is not run; the literature comparison.
- `examples/` — the predicates (`*.cqr`), the certificates (`certs/`), the hardware check files
  (`hw_checks/`), the selections (`hw_select/`), the frontier family (`frontier/`).
- `hw/` — the hardware tools and the committed artifacts (`hw/artifacts/`, `hw/targets/`).
- `CLAUDE.md` — the layout of the Lean packages and the rules of the project; `docs/SORRIES.md` — the
  tracked proof obligations (none open); `docs/PHASE2_SPEC.md`, `docs/PHASE2_ROADMAP.md` — the Phase 2
  specification and roadmap.

## License and citation

Copyright 2026 Aziz F. Zambak. Licensed under the Apache License, Version 2.0 (`LICENSE`). To cite the
work, use `CITATION.cff` (the paper and this repository): Zambak, A. F. (2026). *Certified Quantum
Realization in Lean 4: A Two-Pattern Prototype with Measurement-Based Uncomputation, Validated Routing,
and Conditional Noise Bounds* (Version 1.0). Zenodo. https://doi.org/10.5281/zenodo.24302653. The specification report the project
implements is included in its revisions v2 and v3 (`docs/cqrv_report_revised_v2.docx`,
`docs/cqrv_report_revised_v3.docx`).
