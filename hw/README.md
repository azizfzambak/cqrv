# `hw/` — the hardware backend tools (Track C; PHASE2_SPEC §C)

Untrusted Python tools for the hardware study: they read Qiskit fake backends, lower circuits,
transpile with a witness, run emulations, and compute the figures that Lean re-decides. Nothing in
`hw/` is in the trusted base; the Lean side (`CQRV/Hardware/`, `CQRV/Noise/`) checks what it needs
by the kernel. Nothing anywhere is "verified on hardware" — no device was run; a simulator run is an
emulation; the noise statements are conditional on named premises.

**`.venv-hw`.** The hardware stack (`qiskit`, `qiskit-aer`, `qiskit-ibm-runtime` for its offline fake
backends, with their dependencies) lives in its own git-ignored virtual environment `.venv-hw`, pinned
by `hw/requirements.lock`; the test-harness venv `.venv` and `tests/diff/requirements.lock` are
untouched by it. The download was approved by the author on 2026-11-15 (DECISIONS.md, M4 review); any
other package, pin or calibration data needs a new approval. No IBM account, runtime service or job
submission is used. Recreate it from the lock (Python 3.11, the same as `.venv`):

```
py -3.11 -m venv .venv-hw                          # Windows; `python3.11 -m venv .venv-hw` elsewhere
.venv-hw/Scripts/python.exe -m pip install --no-deps -r hw/requirements.lock
.venv-hw/Scripts/python.exe -m pip check
```

`hw/requirements.txt` lists the three packages unpinned; the lock is `pip freeze` after installing it.
Regenerate the lock only on an approved upgrade. Everything reproduces byte for byte from the recorded
seeds with qiskit 2.6.2 / qiskit-aer 0.18.2 / qiskit-ibm-runtime 0.52.1, whose fake backends carry the
calibration snapshots the targets record.

## 1. The target

`hw/target.py <FakeBackendClass> --out hw/targets/<name>.json` writes a `HardwareTarget`
(`docs/hardware_target.schema.json`): the basis gates, the coupling map, the capabilities
(feed-forward, mid-circuit measurement, reset), the calibration (one- and two-qubit gate errors,
readout errors, T1, T2, as decimal strings read exactly), the durations (ns) and the snapshot hash with
its timestamp. `--feed-forward-off` writes the hand-made coherent-only variant (FakeWashington).
`hw/targets/` holds the two committed targets; `cqr hw capabilities` reads them and checks the snapshot
hash; `cqr hw bound` gives the pre-layout weighted bound; `scripts/check_hw_target.sh` is the CI step.

## 2. Lowering

`hw/lower.py` turns the canonical circuit JSON of the IR into a Qiskit dynamic circuit (`if_test` for
`ifBit`); `tests/diff/hw_lower_check.py` compares Aer with the statevector harness branch by branch
(`scripts/check_hw_lower.sh`). `hw/decomp.py` is **our basis translation**: an explicit table from
every IR gate (and the routing `swap`) to `rz` (exact dyadic angles), `sx`, `x` and `cz` / `cx`, with
one recorded global phase per entry, checked numerically to 1e-12 (`check_table`); the same table is
`CQRV/Hardware/Decomp.lean`, equal to it in CI, and `decomp_sound` is its Lean theorem.

## 3. Transpile with a witness

`hw/transpile.py`: **Qiskit does layout and routing only** — `SabreLayout(coupling_map, seed)` alone
in a `PassManager` (qiskit 2.6.2: layout + routing in one pass, control flow supported, swaps kept,
basis gates untouched). The result is read back (`extract`), matched to the translated elements
through the tracked layout (`witness_of`: an error if the physical order violates a dependency, a gate
or angle differs, or a block does not restore the layout), and rebuilt from the witness alone
(`reconstruct`), which must equal the physical circuit gate for gate. The witness's `clbit_map` is
the identity `[0, …, k−1]` — Qiskit's classical register keeps the IR's bit numbering, and Lean
`ensure`s this explicitly in `applyWitness` / `applyWitnessQ` (revision R15): any other map is
refused with "witness: the classical-bit map is not the identity on the circuit's bits". The swaps are decomposed by the
table (`expand_swaps`); the counts per used qubit and edge give 25a's bound (`physical_bound`, exact
fractions, the n data readouts at their final positions, mid-circuit measurements at the readout rate
by assumption); `seed_search` keeps the seed with the least bound over 0..19. An optional
`coupling_map` routes on a subgraph (Stage 27c, routing (b)).

`hw/artifact.py` writes the artifacts of `hw/artifacts/<instance>__<target>/`: `witness.json`
(`docs/hw_witness.schema.json`), `physical.qasm` (OpenQASM 3), `manifest.json`
(`docs/hw_artifact.schema.json` v1.1.0: the hashes of the certificate JSON when one exists — the full
SHA3-256 of its bytes at transpile time, a historical record that is not compared with the current
certificate.json (R5; the checked binding is the logical circuit's hash) —, of the
canonical logical circuit — the form Lean hashes as `circuit_hash` —, of the target snapshot, of the
witness and of the QASM; the seeds tried; the counts; the bound; `routing` for a subgraph route), and,
with `--extra`, `logical.json` and `physical.json` for the Lean checks (the existing files are checked
byte-identical, never rewritten). `tests/diff/hw_transpile_check.py` (`scripts/check_hw_transpile.sh`)
validates the schemas, reproduces the committed artifacts byte for byte, recomputes the bound from the
QASM and checks the physical circuit's ideal equivalence against the statevector harness. In Lean,
`applyWitness_sound` (Stage 26b3) is the theorem behind the witness; the per-instance check files
(section 5) are its kernel-checked instances.

## 4. Emulator runs

`hw/run.py --sim <artifact dir> --shots N --seed s [--json out] [--md out]` runs a committed artifact
on Aer with `NoiseModel.from_backend(<fake>)` restricted to the used qubits (the mapping is checked
error by error, as channels), the n data qubits read out at their final physical positions into a new
register `r`, and reports p̂ with the 95 % Clopper–Pearson interval, the ideal (noiseless, same shots)
frequency, the reference 1 − δ, δ_hw from the manifest and the one-sided check
p̂ ≥ 1 − δ_hw − √(ln(1/α)/(2·shots)) at α = 0.05 ("vacuous" when δ_hw ≥ 1). The MBU gadget runs in its
wrapped form (`mbu_gadget_wrapped`: |++⟩, the gadget, the inverse of the ideal output's preparation;
success is the all-zero readout). `scripts/hw_runs.sh` runs the full set into `docs/hw_runs/`
(`docs/hw_run.schema.json`, `RUNS.md`); `scripts/check_hw_runs.sh` is the CI step. Every figure is an
**emulator run on the fake backend's noise model**: not a device run, not a validation of a
certificate; the emulator's noise is not of the premises' form (section 7).

## 5. The per-instance checks

`cqr hw check --artifact <dir> --target <target.json>` re-checks the artifact's hashes and writes
`examples/hw_checks/<artifact>/Check.lean`, which the Lean kernel checks with `lake env lean`: the
reconstruction of the physical circuit from the logical one and the witness (`recon`, by `rfl`), its
well-formedness, the coupling edges (`edges_ok`), and the channel theorem at the instance
(`phys_channel`, `phys_zero`), with the standard three axioms. `scripts/check_hw_checks.sh` is the CI
step; `examples/hw_checks/README.md` has the theorems and the kernel times of all fifteen files, and
`docs/BENCHMARKS.md` (R11) every measurement — the physical and conditional certificates' and the
selection files' included — at one commit (`2025ed2`), `lean` run directly, median of 3.

## 6. The physical grade and the physical certificates

`cqr hw grade --artifact <dir> --target <target.json> --ff-latency <ns> [--json]`: the physical grade
(`CQRV/Hardware/PhysGrade.lean`; mirror `hw/physgrade.py`, equal in CI): the qubits used, the two-qubit
count, the mid-circuit measurements, the feed-forward count, the exact wall-clock depth (ASAP; a
conditioned gate waits for its measurement plus the latency L, an assumption every certificate states)
and the exact physical bound (25a's `physical_bound`).

`cqr hw certify --cert <logical cert dir> --artifact <dir> --target <target.json> --ff-latency <ns>`
writes `examples/certs/<cert>_<target>/`: `PhysCert.lean` (self-contained, kernel-checked: the logical
certificate re-derived, the trusted link `emitted_eq : emitted = C`, the reconstruction, the edges, the
channel theorem, **`phys_realizes`** — the realization transferred to the physical circuit from
all-|0⟩ — and the grade at each latency), `physical.qasm` (parsed back to the artifact's gate list by
`tests/diff/hw_physcert_check.py`) and `manifest.json` (schema 1.2.0 since R5: the hashes — the logical
certificate.json cited **modulo `hashes.library` and `reference_configuration`** as `certificate_json_mod_library` /
`certificate_json_sha3_mod_library` (its bytes with the library hash and the object `reference_configuration`
— toolchain, machine and timing fields — set to null, so that a library change moves only the `library`
fields and a re-measurement (R11, `scripts/bench_all.py`) moves no hardware file; the key name is R5's), and `hashes.library`, the SHA3-256 of the CQRV sources the files were
generated against (`CQRV.Certify.libraryHash`; `tests/diff/libhash.py` warns when a recorded hash is not the
tree's and blocks with `--release`) —, the grades, the
status words `logical_certified`, `hardware_compatible`, `physical_translation_validated`,
`emulator_sanity_checked` (R3; `emulator_validated` before: the emulator's noise model is not of the
(P-stoch) form, so a pass is a sanity check, not evidence for the premise) only when the run report
passed, `model_premises` (R4: `ideal_device`, `P-prep`, `P-ctrl`, one sentence each; the conditional
certificates state `P-prep`, `P-ctrl` and replace `ideal_device` by `noise.premises`), and
`meaning_physical_translation`: on an ideal
device with these gates and this connectivity, started from all-|0⟩, the physical circuit realizes the
specification — not a statement about noise).

`cqr hw select --request <name> --target <target.json> --prefer twoq|depth|bound|noise [--ff-latency <ns>]
[--budget X] [--out <dir>] [--table]` selects among a request's artifacts by a grade component
(`selectPhys`, `selectPhys_spec`; the four committed `examples/hw_select/*/Select.lean` are
kernel-checked) or by the noise bound (`selectNoise`, no file written); a budget no candidate meets
returns `none`. `scripts/check_physcert.sh` is the CI step "Physical certificate".

## 7. The noise bound and the conditional certificates

`cqr hw noise --artifact <dir> --target <target.json> [--json]` computes `noiseBound = δ + Σ p_g + Σ r_j`
(`CQRV/Hardware/Noise.lean`; mirror `hw/noisebound.py`, equal on all artifacts in CI) under the four
premises: **(P-cal)** the rates are the target file's snapshot, shipped with qiskit-ibm-runtime and
recorded from a real device on a past date; **(P-stoch)** every basis operation on k qubits is ideal with
probability `1 − p_g`, `p_g = min 1 ((d+1)/d · r_g)`, d = 2^k (3/2 · r one-qubit, 5/4 · r two-qubit;
virtual `rz` has r = 0), and otherwise an arbitrary channel on the whole register; **(P-ro)** every
measurement and data readout is ideal with probability `1 − r_j`; **(P-idle)** only the listed
operations act. `clamped` says whether some p reached the clamp (then the bound is vacuous). The
theorem behind it is `phys_noisy_stochastic` (`CQRV/Noise/Stochastic.lean`, on 27a's step semantics):
for every choice of the arbitrary channels, the noisy physical channel realizes the specification with
δ'.

`cqr hw noisecert --artifact <dir> --target <target.json> --ff-latency <ns> [--cert <logical cert dir>] [--out <dir>]`
writes a **conditional certificate**: with `--cert`, `PhysCert.lean` plus the noise block (the
probabilities `ps`, `rs` and `noiseB` as literals, `noiseBound_eq` and `noise_key` by the kernel, and
`phys_noisy_inst`: for every choice of the arbitrary channels the noisy physical channel realizes the
specification with δ' = `noiseB`); without, the channel form of the bare MBU gadget (`NoiseCert.lean`:
`c_eq : C = mbuCircuit` by the kernel, `gadget_noisy`). The manifest names `noise_conditional`, the
four premises, the meaning sentence (conditional on the premises, the device's success probability is
at least 1 − δ'; the premises are assumptions about the device, not facts proved here) and the
emulator comparison at δ' from the recorded run (25b's criterion with its recorded margin,
`threshold' = threshold + δ_hw − δ'`, with the full protocol — α, shots, seed, successes, p̂ = successes/shots,
the one-sided Hoeffding margin `sqrt(ln(1/α) / (2·shots))` as formula and float, the recorded margin
actually used — in `emulator_comparison` (R3); `emulator_sanity_checked` only on a pass; "no run recorded for this
artifact" otherwise). The committed conditional certificates: hw_n2 (δ' 0.1793), hw_n3 (0.7521), the
gadget (0.0995) and the three frontier instances (section 8). `scripts/check_noisecerts.sh` is the CI
step "Noise certificates".

## 8. The feasibility frontier

`python -I scripts/frontier.py --cqr <cqr> --series <target>:<mode>:<routing>` (`.venv-hw`) runs one
series of the family `examples/frontier/fr_n<k>.cqr` (Grover on k ANDs, M = 1, r = r⋆, k = 2…7) in a
mode (`tree_mbu`, `tree_coherent`, `fewlog_mbu`) and a routing (`a` the full coupling map; `b` the
edges of calibrated error ≥ 1/2 removed, largest connected component), with the early stop after two
consecutive vacuous n; the scratch artifacts go to `.lake/frontier/` and the rows to
`docs/hw_frontier/frontier.json` (from `cqr hw grade` and `cqr hw noise`, no kernel). `--render` writes
`docs/hw_frontier/FRONTIER.md`: the frontier per (target, mode, routing) — the largest n whose
`noiseBound` is below 1: n = 3 on FakeTorino in every mode, n = 2 on FakeWashington —, the full table,
and the idle-exposure diagnostic (each used qubit's idle time under the ASAP schedule over its T2;
reported, not part of any bound: it shows how far (P-idle) is from a device). `--promote` copies a
scratch artifact into `hw/artifacts/` for a frontier certificate. The Qiskit regeneration is by hand;
`tests/diff/hw_frontier_check.py` (in the step "Noise certificates") checks the committed rows and
certificates.
