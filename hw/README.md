# `hw/` — the hardware backend tools (Track C; PHASE2_SPEC §C)

Untrusted Python tools for the hardware study: they read Qiskit fake backends, lower circuits
and run simulations, and produce witnesses that Lean checks. Nothing in `hw/` is in the trusted
base, and nothing here is "verified on hardware" — a simulator run is an emulation.

## `.venv-hw`

The hardware stack (`qiskit`, `qiskit-aer`, `qiskit-ibm-runtime` for its offline fake backends,
with their dependencies) lives in its own git-ignored virtual environment `.venv-hw`, pinned by
`hw/requirements.lock`. The test-harness venv `.venv` and `tests/diff/requirements.lock` are
untouched by it. The download was approved by the author on 2026-11-15 (DECISIONS.md, M4 review);
any other package, pin or calibration data needs a new approval. No IBM account, runtime service or
job submission is used.

Recreate it from the lock (Python 3.11, the same as `.venv`):

```
py -3.11 -m venv .venv-hw                          # Windows; `python3.11 -m venv .venv-hw` elsewhere
.venv-hw/Scripts/python.exe -m pip install --no-deps -r hw/requirements.lock
.venv-hw/Scripts/python.exe -m pip check
```

`hw/requirements.txt` lists the three packages unpinned; the lock is `pip freeze` after
installing it. Regenerate the lock only on an approved upgrade.

## Tools

- `hw/target.py` (Stage 24a): `python -I hw/target.py <FakeBackendClass> --out hw/targets/<name>.json`
  writes a `HardwareTarget` (`docs/hardware_target.schema.json`); `--feed-forward-off` writes the
  hand-made coherent-only variant. `hw/targets/` holds the committed targets; `cqr hw capabilities`
  reads them and checks the snapshot hash; `scripts/check_hw_target.sh` is the CI step.
- `hw/lower.py` (Stage 24b): the canonical circuit JSON of the IR → a Qiskit dynamic circuit
  (`if_test` for `ifBit`); `tests/diff/hw_lower_check.py` compares Aer with the statevector harness
  branch by branch (`scripts/check_hw_lower.sh`).
- `cqr hw bound` (Stage 24c, Lean): the pre-layout weighted bound under the decomposition table and
  the device's worst-case rates; `tests/diff/hw_bound_check.py` recomputes it.

## The transpile pipeline with a witness (Stage 25a)

1. `hw/decomp.py` — **our basis translation**: an explicit table from every IR gate (and the
   routing `swap`) to `rz` (exact dyadic angles), `sx`, `x` and `cz` / `cx`, with one recorded
   global phase per entry, checked numerically to 1e-12 (`check_table`); a conditioned IR gate
   becomes one `if_test` block holding its basis sequence; every basis gate carries its provenance.
2. `hw/transpile.py` — **Qiskit does layout and routing only**: `SabreLayout(coupling_map, seed)`
   alone in a `PassManager` (qiskit 2.6.2: layout + routing in one pass, control flow supported,
   swaps kept as `swap`, basis gates untouched). The result is read back (`extract`), matched to the
   translated elements through the tracked layout (`witness_of`: an error if the physical order
   violates a dependency, a gate or angle differs, or a block does not restore the layout), and
   rebuilt from the witness alone (`reconstruct`), which must equal the physical circuit gate for
   gate. The swaps are then decomposed by the table (`expand_swaps`), the counts per used qubit
   and edge give the bound on the physical circuit (`physical_bound`, exact fractions, the n data
   readouts at their final positions, mid-circuit measurements at the readout rate by assumption),
   and `seed_search` keeps the seed with the least bound over a fixed list.
3. `hw/artifact.py` — the artifacts of `hw/artifacts/<instance>__<target>/`: `witness.json`
   (`docs/hw_witness.schema.json`), `physical.qasm` (OpenQASM 3) and `manifest.json`
   (`docs/hw_artifact.schema.json`: hashes of the certificate JSON, the canonical logical circuit,
   the target snapshot, the witness and the QASM; the seeds tried; the counts; the bound).
   Regenerate them with `python -I hw/artifact.py --cqr .lake/build/bin/cqr.exe`.
4. `tests/diff/hw_transpile_check.py` (`scripts/check_hw_transpile.sh`): the table, the committed
   artifacts reproduced byte for byte, the hashes, the bound recomputed from the QASM, and the
   ideal-equivalence check of the physical circuit against the statevector harness.

Everything here is reported, not certified; Stage 26 checks the witness in Lean.

## Emulator runs on the fake backends' noise models (Stage 25b)

`hw/run.py --sim <artifact dir> --shots N --seed s [--json out] [--md out]` runs a committed physical
artifact on Aer with `NoiseModel.from_backend(<fake>)` restricted to the used qubits (the mapping is
checked error by error, as channels), the n data qubits read out at their final physical positions
into a new register `r` (the IR has no final readout), and reports p̂ with the 95 % Clopper–Pearson
interval, the ideal (noiseless, same shots) frequency, the reference 1 − δ, δ_hw from the manifest
and the one-sided check p̂ ≥ 1 − δ_hw − √(ln(1/α)/(2·shots)) at α = 0.05 ("vacuous" when δ_hw ≥ 1).
The MBU gadget is run in its wrapped form (`mbu_gadget_wrapped`, its own artifact: |++⟩, the gadget,
then the inverse of the ideal output's preparation; success is the all-zero readout). Mid-circuit
measurements carry the readout error — the Stage 24c assumption. `scripts/hw_runs.sh` runs the full
set and writes `docs/hw_runs/RUNS.md` with the per-run JSONs (`docs/hw_run.schema.json`);
`scripts/check_hw_runs.sh` is the CI step (the three small instances at 2000 shots). Every figure is
an **emulator run on the fake backend's noise model**: not a device run, not a validation of a
certificate, and never "verified on hardware".

## The per-instance kernel checks (Stage 26c1b)

Each artifact directory also holds `logical.json` (the canonical logical circuit, whose SHA3-256 is
the manifest's `logical_circuit`) and `physical.json` (the final physical circuit on the device
qubits), written by `python -I hw/artifact.py --cqr <cqr> --extra` from the recorded seeds (the
existing files are checked byte-identical, never rewritten). From them, `cqr hw check --artifact
<dir> --target <target.json>` re-checks the hashes and writes `examples/hw_checks/<artifact>/Check.lean`,
which the Lean kernel checks with `lake env lean`: the reconstruction of the physical circuit from
the logical one and the witness (`recon`), its well-formedness, the coupling edges (`edges_ok`), and
the channel theorem at the instance (`phys_channel`, `phys_zero`), with the standard three axioms.
`scripts/check_hw_checks.sh` is the CI step; `examples/hw_checks/README.md` has the theorems and
the measured kernel times. Nothing is "verified on hardware": the physical circuit is validated
against the logical one on the target's coupling map.

## The physical grade and the physical certificate (Stage 26c2)

`cqr hw grade --artifact <dir> --target <target.json> --ff-latency <ns> [--json]` computes the
physical grade of an artifact's circuit: the qubits used, the two-qubit count, the mid-circuit
measurements, the feed-forward count, the exact wall-clock depth (ASAP; the durations are the exact
rationals of the target file's decimals; a conditioned gate waits for its measurement plus the
latency L, an assumption the certificate states) and the exact physical bound (25a's
`physical_bound`). `hw/physgrade.py` is its Python mirror; `tests/diff/hw_physgrade_check.py`
checks equality on all artifacts at L = 0 and 1000 ns.

`cqr hw certify --cert <logical cert dir> --artifact <dir> --target <target.json> --ff-latency <ns>`
writes `examples/certs/<cert>_<target>/`: `PhysCert.lean` (self-contained; checked by the kernel
with `lake env lean`: the logical certificate re-derived, `emitted = C`, the reconstruction, the
edges, the channel theorem, the realization transferred to the physical circuit from all-|0⟩, the
grade at each latency), `physical.qasm` (the file one would run; `tests/diff/hw_physcert_check.py`
parses it back to the artifact's gate list) and `manifest.json` (hashes — including the target
file's bytes, since the durations are outside the snapshot hash —, grades, status words). The
status words are `logical_certified`, `hardware_compatible`, `physical_translation_validated`,
`emulator_validated` (only when the run report passed). "Physically validated" means: on an ideal
device with these gates and this connectivity, started from all-|0⟩, the physical circuit realizes
the specification. Noise is Stage 27; nothing is "verified on hardware".

`cqr hw select --request <name> --target <target.json> --prefer twoq|depth|bound [--ff-latency <ns>]
[--budget X] [--out <dir>] [--table]` (Stage 26c2b) grades a request's committed artifacts on the
target and chooses the first minimal admissible one (`selectPhys`, `selectPhys_spec`: mbu needs the
target's feed-forward; the budget, if given, bounds the component). It writes
`examples/hw_select/<request>__<target>/Select.lean`, where the kernel re-decides every grade and the
choice; each candidate is linked by its `physical.json` hash to its `examples/hw_checks/<artifact>/Check.lean`.
`--table` prints the choice under every preference. A budget no candidate meets returns `none`: on
FakeTorino every bound is vacuous, so `--budget 1` admits nothing — the honest answer, not an error.
The CI step "Physical certificate" (`scripts/check_physcert.sh`, pass mark 25) runs the three Python
checks and the kernel on the certificate and the four selections.

## The conditional noise bound (Stage 27b)

`cqr hw noise --artifact <dir> --target <target.json> [--json]` computes `noiseBound = δ + Σ p_g + Σ r_j`
(`CQRV/Hardware/Noise.lean`; mirror `hw/noisebound.py`; equality on all artifacts by
`tests/diff/hw_noise_check.py`): under (P-stoch) every basis operation on k qubits is ideal with
probability `1 − p_g`, `p_g = min 1 ((d+1)/d · r_g)`, d = 2^k (3/2 · r one-qubit, 5/4 · r two-qubit;
virtual `rz` has r = 0), and otherwise an arbitrary channel on the whole register; under (P-ro) every
measurement and data readout is ideal with probability `1 − r_j`; (P-idle) only the listed steps act;
(P-cal) the rates are the target file's snapshot. `clamped` says whether some p reached the clamp
(then the bound is vacuous). `cqr hw select --prefer noise` selects by it (`selectNoise`, no file
written). The theorem behind it is `phys_noisy_stochastic` (`CQRV/Noise/Stochastic.lean`): for every
choice of the arbitrary channels, the noisy physical channel realizes the specification with δ'.
Conditional on the premises, which are assumptions about the device, not facts proved here; the
emulator's noise model is not of the (P-stoch) form; nothing is "verified on hardware".

`cqr hw noisecert --artifact <dir> --target <target.json> --ff-latency <ns> [--cert <logical cert dir>] [--out <dir>]`
(Stage 27b2) writes a **conditional certificate**: with `--cert`, 26c2's `PhysCert.lean` plus the noise
block — the probabilities `ps`, `rs` and the bound `noiseB` as literals, `noiseBound_eq` and
`noise_key` decided by the kernel, and `phys_noisy_inst` (for every choice of the arbitrary channels
the noisy physical channel realizes the specification with δ' = `noiseB`); without, the channel form of
the bare MBU gadget (`NoiseCert.lean`: `c_eq : C = mbuCircuit` by the kernel, `gadget_noisy`). The
manifest names the status word `noise_conditional`, the four premises and the meaning sentence, and
the emulator comparison at δ' from the recorded run (25b's criterion with its recorded margin:
`threshold' = threshold + δ_hw − δ'`; `emulator_validated` only on a pass; "no run recorded for this
artifact" otherwise). The CI step "Noise certificates" (`scripts/check_noisecerts.sh`, pass mark 26)
kernel-checks the five Lean files and runs the two Python checks. Conditional on the premises, which
are assumptions about the device, not facts proved here; nothing is "verified on hardware".

## The feasibility frontier (Stage 27c)

`python -I scripts/frontier.py --cqr <cqr> --series <target>:<mode>:<routing>` (`.venv-hw`) runs one
series of the family `examples/frontier/fr_n<k>.cqr` (Grover on k ANDs, M = 1, r = r⋆, k = 2…7) in a
mode (`tree_mbu`, `tree_coherent`, `fewlog_mbu`) and a routing (`a` the full coupling map with the seed
search 0..19; `b` the edges of calibrated error ≥ 1/2 removed, largest connected component), with the
early stop after two consecutive vacuous n; the scratch artifacts go to `.lake/frontier/` and the rows
to `docs/hw_frontier/frontier.json` (from `cqr hw grade` and `cqr hw noise`, no kernel). `--render`
writes `docs/hw_frontier/FRONTIER.md`: the frontier per (target, mode, routing) — the largest n whose
`noiseBound` is below 1 —, the full table, and the idle-exposure diagnostic (each used qubit's idle
time under the ASAP schedule over its T2; reported, not part of any bound). `--promote <row>:<target>`
copies a scratch artifact into `hw/artifacts/` and prints the certificate commands (`cqr certify`,
`cqr hw check`, `cqr hw noisecert`). The Qiskit regeneration is by hand; CI checks the committed rows
and certificates (`tests/diff/hw_frontier_check.py`, in the step "Noise certificates"). Nothing here is
"verified on hardware".

