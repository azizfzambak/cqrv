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
