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
