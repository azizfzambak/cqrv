# Release notes — reproduction and the trust boundary (Stage 30b, 2026-11-16)

PHASE2_SPEC §D.3. What a reader needs to rebuild CQRV, re-run its checks and know what is proved,
what is checked, what is untrusted and what is assumed. Nothing in this repository is "verified on
hardware": no device was run; every hardware figure is an emulation or a conditional bound.

## 1. Reproduction

### 1.1 The toolchain and the dependency pins

- Lean: `leanprover/lean4:v4.35.0` (`lean-toolchain`), installed with elan.
- Lake dependencies (`lake-manifest.json`, never bumped ad hoc — CLAUDE.md rule 4): Mathlib at the
  `v4.35.0` tag (`56a005855ea1…`), Physlib `96a6bc5e3c50…`, with their transitive packages
  (batteries, aesop, Qq, proofwidgets, importGraph, LeanSearchClient, plausible, Cli) at the revisions
  the manifest records. `lake exe cache get` fetches the Mathlib oleans.
- Python 3.11 (two virtual environments, both git-ignored, both installed with `--no-deps` from a
  lock):
  - `.venv` from `tests/diff/requirements.lock` — the test harness (numpy, scipy, jsonschema 4.26.0,
    llvmlite for the QIR re-parse, …);
  - `.venv-hw` from `hw/requirements.lock` — the hardware tools: qiskit 2.6.2, qiskit-aer 0.18.2,
    qiskit-ibm-runtime 0.52.1 (its offline fake backends; **their calibration snapshots are the ones
    shipped with that version**, recorded from real devices on past dates — the targets' `snapshot`
    field has the timestamp and the SHA3-256 hash), numpy 2.4.6, scipy 1.17.1. No IBM account, token
    or job submission is used anywhere.

```
export LEAN_NUM_THREADS=4          # Windows: avoids out-of-memory with one Lean per core
lake exe cache get && lake build   # the library, the tests and the cqr executable
py -3.11 -m venv .venv    && .venv/Scripts/python.exe    -m pip install --no-deps -r tests/diff/requirements.lock
py -3.11 -m venv .venv-hw && .venv-hw/Scripts/python.exe -m pip install --no-deps -r hw/requirements.lock
```

(`python3.11 -m venv …` and `.venv/bin/python` on Linux.)

### 1.2 The CI, step by step

`scripts/ci_local.sh` runs the 26 local steps of `.github/workflows/ci.yml` in order and prints one
line per step; the pass mark is **26 PASS, 0 FAIL, 4 n/a**. CI is local by decision (DECISIONS.md,
2026-10-25); the workflow file is the same step list for a remote runner. Each step is a script that
can be run alone, after `lake build`:

| Step | Command | What it checks | Time (s, the 30a acceptance run) |
|---|---|---|---|
| 4 | `lake build` | the library, tests, cqr; warning-free | — |
| 6 | `scripts/check_sorries.sh [--self-test]`; `scripts/check_layering.sh` | 0 tracked sorry; no Circuit/Synthesis → Grover import | 91 |
| 7 | `scripts/cli_smoke.sh` | every cqr subcommand on the examples, outputs byte-identical to the expected ones | 127 |
| 8 | `scripts/print_axioms.sh` | `#print axioms` of every committed certificate: exactly the standard three (`sorryAx`, `ofReduceBool` rejected) | 211 |
| 10–14 | `tests/diff/statevector.py --selftest`, `scripts/diff_oracles.sh`, `scripts/diff_frontend.sh`, `scripts/check_oracle_json.sh` | the statevector harness; synthesized oracles against it for n ≤ 12; the front end; the golden circuits | — |
| 15–19 | `scripts/diff_grover.sh`, `diff_mcz.sh`, `diff_qft.sh`, `diff_counting.sh`, `diff_benchmark.sh` | the Grover, few-ancilla MCZ, QFT / AQFT and counting circuits against the harness; the second predicate | — |
| 21 | `scripts/check_emit.sh` | SHA3 hashes, the certificate schema, QIR / QASM re-parse | — |
| 22 | `scripts/check_certify.sh` | `cqr certify` on both predicates and few:log, the counting certificate, the negative tests; kernel checks | 680 |
| 23 | `scripts/check_select.sh` | certified selection | 152 |
| 24 | `scripts/check_hw_target.sh` | the two targets against `docs/hardware_target.schema.json`; the snapshot hash by Lean | 18 |
| 25 | `scripts/check_hw_lower.sh` | the lowering to Qiskit against the harness, branch by branch (18 instances) | 61 |
| 26 | `scripts/check_hw_transpile.sh` | the artifact and witness schemas; the eleven 25a artifacts reproduced byte for byte from their seeds; the bound recomputed; ideal equivalence | 122 |
| 27 | `scripts/check_hw_runs.sh` | the recorded emulator runs (the three small instances re-run at 2000 shots) | 37 |
| 28 | `scripts/check_hw_checks.sh` | the fifteen `examples/hw_checks/*/Check.lean` regenerated and kernel-checked | 298 |
| 29 | `scripts/check_physcert.sh` | `PhysGrade` Lean = Python; the 26c2 certificate and the four selections regenerated and kernel-checked | 137 |
| 30 | `scripts/check_noisecerts.sh` | `noiseBound` Lean = Python on all artifacts; the six conditional and five logical certificate files regenerated / kernel-checked; the frontier rows | 164 |

Steps 1, 2, 9, 20 (checkout, elan, setup-python, apt install of llvm) have no local counterpart. The
times are the reviewer's acceptance run of Stage 30a (2026-11-16; `.lake/ci_local/`); step 22 varies
from 675 to about 1 000 s with machine load.

### 1.3 What reproduces byte for byte

- **Every certificate** (`examples/certs/*/Cert.lean`, `certificate.json`, `PhysCert.lean`,
  `NoiseCert.lean`, `physical.qasm`, `manifest.json`), every check file (`examples/hw_checks/*/Check.lean`)
  and every selection file (`examples/hw_select/*/Select.lean`) is regenerated by the corresponding
  `cqr` subcommand in CI and compared byte for byte with the committed file (steps 7, 22, 23, 28, 29,
  30). The `reference_configuration` field of a `certificate.json` (machine, kernel time) is the only
  field that depends on the machine, and `cqr certify` writes it from the current run.
- **The eleven 25a artifacts** (`hw/artifacts/*/witness.json`, `physical.qasm`) reproduce byte for byte
  from their recorded seed with qiskit 2.6.2 (`hw/artifact.py --extra`; step 26). The three frontier
  artifacts (`fr_*`) are checked through their check files and certificates (steps 28, 30); the
  frontier table itself (`docs/hw_frontier/FRONTIER.md`) is regenerated by hand
  (`scripts/frontier.py --series …`, about a minute of Qiskit for all 30 rows) and its committed rows
  are checked against `cqr hw noise` / `cqr hw grade` in step 30.
- **The emulator runs** (`docs/hw_runs/*.json`) are seeded (seed 25) and the three small ones are
  re-run in step 27; Aer's floating-point results are reproducible on one platform and version, not
  guaranteed across platforms.
- The kernel times (`kernel_check`, the CI step times) are measurements on the reference machine
  and are not expected to reproduce; the axiom lines are.

### 1.4 Using the tool

```
lake exe cqr certify examples/grover_pred_037.cqr --report                       # a Grover certificate
lake exe cqr certify examples/grover_pred_037.cqr --problem count --precision 4  # a counting certificate
lake exe cqr certify examples/grover_pred_037.cqr --budget 12,200,100,8 --prefer depth
lake env lean examples/certs/grover_pred_037/Cert.lean                           # check it yourself
lake exe cqr hw check    --artifact hw/artifacts/hw_n3_tree_mbu__fake_torino --target hw/targets/fake_torino.json
lake exe cqr hw certify  --cert examples/certs/hw_n3 --artifact hw/artifacts/hw_n3_tree_mbu__fake_torino --target hw/targets/fake_torino.json --ff-latency 1000
lake exe cqr hw noisecert --cert examples/certs/hw_n3 --artifact hw/artifacts/hw_n3_tree_mbu__fake_torino --target hw/targets/fake_torino.json --ff-latency 1000
lake env lean examples/certs/hw_n3_torino/PhysCert.lean                          # the conditional certificate
```

## 2. The trust boundary

### 2.1 What the kernel checks

Everything a `Cert.lean`, `PhysCert.lean`, `NoiseCert.lean`, `Check.lean` or `Select.lean` states,
checked by `lake env lean` with `#print axioms` naming exactly `propext`, `Classical.choice`,
`Quot.sound` (none for the trusted links `emitted_eq`, `c_eq`); `native_decide` is never used, and
the axiom audit rejects `Lean.ofReduceBool` and `sorryAx`:

- the front end at the instance (`toNetwork prog = .ok net`, `front_end`) — the typed term's
  translation to the network, not its parsing;
- the synthesizer's output at the instance (`emitted_ok`: the kernel re-runs the synthesizer on the
  network literal), the grade (`grade_eq`, `gradeExt_eq`), the solution count (`hM_count`), the exact
  δ (`delta_eq`), and the theorem `cert` — `RealizesExact` of the specification by the emitted circuit's
  channel, with ancilla restoration — as an instance of the pattern's parametric lemma;
- for selection, that the chosen candidate fits the budget and no admissible candidate has a smaller
  key (`chosen_fits`, `selected`; `select_spec`);
- for a routed circuit, that the artifact's logical circuit is the certified one (`emitted_eq`), that
  the witness reconstructs the physical circuit (`recon`, by `rfl`), that every two-qubit gate is on a
  coupling edge (`edges_ok`), that the physical circuit's channel on the embedded input is the embedded
  logical output (`phys_channel`, `phys_zero`), that the realization transfers to the physical circuit
  from all-|0⟩ (`phys_realizes`), the physical grade (`physGrade_L0`, `physGrade_L1000`), and — in a
  conditional certificate — the probabilities, the exact bound and the noisy realization for every
  choice of the arbitrary channels (`ps_eq`, `rs_eq`, `noiseBound_eq`, `noise_key`, `phys_noisy_inst`;
  `gadget_noisy` in the channel form).

Behind these instances stand the library theorems of `CQRV/` (the report's Theorems 3.3a/b, Lemma
6.3.2, the Grover and amplitude-estimation lemmas, the matcher's soundness and completeness on its
fragment, the Track B theorems, `translate_sound`, `applyWitness_sound`, `channelDenote_eq_steps`,
`phys_noisy_stochastic`), all sorry-free and pinned by `#guard_msgs` in `tests/CQRVTests/`
(`docs/M5_REPORT.md` §1.1).

### 2.2 What is untrusted

- The **parser, surface checker and typed-term printer** of the DSL (the `predicate_hash` binds the
  source; the typed term is a literal in the certificate).
- The **spec extraction ℰ and the matcher's run** (the theorem restates the instance; the matcher is
  proved sound and complete for its fragment, but its execution is not kernel-checked).
- The **emitters** (QIR, OpenQASM 3, `physical.qasm`): translation-validated by re-parse, not
  verified.
- **Qiskit** (`SabreLayout`, the fake backends, `qasm3`), **Aer** and every Python tool in `hw/` and
  `tests/diff/`: they produce witnesses, artifacts, mirrors and runs; Lean re-decides what it needs
  from literals and hashes; the mirrors (`physgrade.py`, `noisebound.py`) are checked equal to the Lean
  functions, not trusted.
- The **statevector harness** (`tests/diff/statevector.py`) is a differential check of the untrusted
  Python side; it is not part of any proof.
- Lean's own trusted base: the kernel, the pinned toolchain, Mathlib and Physlib at their pinned
  revisions, and the `#guard_msgs`/`#print axioms` discipline.

### 2.3 What is a premise

Hypotheses of theorems, named in every conditional certificate's manifest (`noise.premises`); never
facts about a device:

- **(P-cal)** the calibration is the target file's snapshot (`hw/targets/*.json`), shipped with
  qiskit-ibm-runtime 0.52.1 and recorded from a real device on a past date (the `snapshot.timestamp`);
  not a live calibration.
- **(P-stoch)** every basis operation on k qubits is, with probability at least 1 − p, its ideal
  channel and otherwise an arbitrary channel on the whole register, with p = min 1 ((d+1)/d · r),
  d = 2^k, r its calibrated error — the Pauli reading of a randomized-benchmarking error; virtual `rz`
  has r = 0; `clamped` records when the clamp is reached.
- **(P-ro)** every readout, mid-circuit measurements included, is with probability at least 1 − r its
  ideal channel and otherwise arbitrary, with r the calibrated readout error.
- **(P-idle)** idle qubits suffer no error — the premise furthest from a device; the idle-exposure
  diagnostic (`FRONTIER.md`) shows how far.
- **The feed-forward latency L** (0 and 1 000 ns in every physical certificate): an assumption about
  timing that enters the depth, not the bound.
- Also stated, not assumed: the hardware bound of 24c/25a (`p = r`, the sum of rates) is a reported
  figure, not a theorem's bound; the emulator comparison is a sanity check (Aer's noise model is not
  of the (P-stoch) form).

The physical statement of a certificate (`meaning_physical_translation`) is unconditional on an ideal
device with the target's gates and connectivity; the conditional statement (`noise.meaning`) is
conditional on the four premises. The frontier (`docs/hw_frontier/FRONTIER.md`) says where the
conditional bound is below 1 on the two fakes: up to n = 3 ANDs on FakeTorino, n = 2 on
FakeWashington.

## 3. Status of the release (v1.0.0, 2026-11-17)

By the author's decisions of 2026-11-17 (`docs/DECISIONS.md`), the repository is published with its full
history under the Apache License 2.0 (`https://github.com/azizfzambak/cqrv`, tag `v1.0.0`), and the unified paper (`paper/`) is
published as a preprint on Zenodo (all versions: https://doi.org/10.5281/zenodo.24302652; version 1.0: https://doi.org/10.5281/zenodo.24302653). Version 1.1 (tag `v1.1.0`) corrects the paper after three AI-generated reviews (`docs/REVIEW_RESPONSE_2.md`). The code the paper describes is commit `2f8200b`; the tag adds only
documentation, so no `.lean` file and no certificate changed. No container image is provided: reproduction
uses the pins and the steps of §1. The human expert audit of the main definitions (REVIEW_RESPONSE_1, R14)
was not done, by the author's decision. Stage 28 (device runs) is not run, by the author's decision of
2026-11-16 (PHASE2_SPEC §D.1). Stage 29 is not run (`docs/STAGE29_NOTE.md`).
