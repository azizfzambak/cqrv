# Stage 24 — Target model and lowering (PHASE2_SPEC §C.1; Track C, Paper 1)

PHASE2_SPEC.md §C, §C.1. Report: §3.1.3, §5.3. PHASE2_ROADMAP row 24. Written at the M4 review
(2026-11-15) by the reviewer, under the author's delegation.

Stage 24 has three tasks, one commit each:
- **24a**, the environment, the target model and `cqr hw capabilities`, is specified here;
- **24b**, the lowering and the comparison on Aer, and **24c**, the per-operation rates, are
  outlined and get their detailed text at the review of the task before them.

Precondition: main = the M4 review commit. Start with `git switch -c stage-24a main`. Untracked
and not yours: `docs/paper/`, `docs/cqrv_report_revised_v4.docx`. Windows: `LEAN_NUM_THREADS=4`.

The process is the delegated one:
1. The reviewer session sends the prompt.
2. You implement, and say "ready for CI".
3. The reviewer audits and runs CI.
4. You commit on the reviewer's prompt.

**Invariants of Stage 24.**
- **No existing theorem statement changes.** No committed certificate is regenerated, and the
  search and counting outputs of `cqr` stay byte-identical. `cqr hw` is a new subcommand; every
  other subcommand is untouched.
- **The `cqr` closure stays Lean core + Mathlib.** New Lean modules for the target JSON are
  Physlib-free.
- **`.venv` and `tests/diff/requirements.lock` are untouched.** The hardware stack lives in
  `.venv-hw`, added to `.gitignore`, pinned by `hw/requirements.lock`.
- **The download.** The author approved, in the reviewer's session on 2026-11-15, qiskit,
  qiskit-aer and qiskit-ibm-runtime (for the offline fake backends only), with their
  dependencies, from PyPI into `.venv-hw`. Your standing rule still applies: confirm with the user
  directly, in your session, before running pip. Tell the user the package list, the source and
  the size that pip reports. No other download.
- **No network use beyond that pip install.** No IBM account, no runtime service, no job
  submission.
- **No `sorry`.** If a statement here is false, give the counterexample and the corrected form.
  CLAUDE.md rule 2 applies to Lean names; for Qiskit APIs, check them in the installed version
  (`python -c "import qiskit; help(...)"`), not from memory.

---

## 24a — The environment, the target model, `cqr hw capabilities`

### R1. The environment

- Create `.venv-hw`, with the same Python as `.venv` (3.11), and add it to `.gitignore`.
- Write `hw/requirements.txt` (qiskit, qiskit-aer, qiskit-ibm-runtime, unpinned). After the
  user's confirmation, install from it.
- Freeze the result into `hw/requirements.lock`, with the same header style as
  `tests/diff/requirements.lock`.
- Record the resolved versions and the download size in (c).
- `hw/README.md` (short): what `.venv-hw` is, how to recreate it from the lock, and that every
  tool in `hw/` is untrusted.

### R2. `HardwareTarget`

- **The schema** `docs/hardware_target.schema.json`, version 1.0.0, with the fields of
  PHASE2_SPEC §C.1. Every flag and every calibration field records where it came from (a
  `source` string per group).
- **`hw/target.py`.** `extract(backend) -> dict`, and a CLI
  `python -I hw/target.py <FakeBackendClass> --out hw/targets/<name>.json`.
  - It reads the basis gates, the coupling map, the durations and errors from `backend.target`,
    and T1 / T2 from the qubit properties.
  - The capabilities come from whether the target supports `if_else`, `measure` and `reset`.
  - If the backend gives no mid-circuit measurement error, the field is null with a note.
  - It writes the canonical JSON: sorted keys, compact, then a trailing newline.
  - The `snapshot.hash` is SHA3-256 over the canonical JSON of `calibration`, from Python's
    `hashlib.sha3_256`.
- **Two committed targets in `hw/targets/`.** Pick two fake backends from the installed
  `qiskit_ibm_runtime.fake_provider`:
  - one that supports dynamic circuits (`if_else` in its target);
  - and, if the installed fakes contain one, one that does not.

  If every fake supports `if_else`, the second is a copy of the first with
  `feed_forward: false`, marked as a hand-made variant in its `source`. It exercises the
  `coherent`-only path. Say which you chose.

### R3. Lean: reading a target, `cqr hw capabilities`

- **`CQRV/Hardware/Target.lean`** (new, Physlib-free). It holds `HardwareTarget` (the fields
  Lean needs: name, num_qubits, basis_gates, coupling_map, capabilities, the snapshot hash) and
  `HardwareTarget.ofJson`. It also holds `HardwareTarget.checkHash`: Lean's SHA3-256 of the
  canonical `calibration` must equal `snapshot.hash`.
  - The canonical form must be byte-identical between Python and Lean. Test it on both committed
    targets.
  - If a number's printing differs (floats), store the calibration numbers as decimal strings,
    or hash the bytes of the `calibration` substring exactly as written. Choose one, record it,
    and make both sides agree.
- **`cqr hw capabilities <target.json>`.** It prints:
  - the name;
  - the three capability flags with their sources;
  - `uncompute modes: mbu, coherent` or `uncompute modes: coherent`;
  - the hash check (`snapshot hash ok`, or the mismatch and exit 1).

  Usage errors exit 2. The usage text lists `hw capabilities`.

### R4. Checks

- **`tests/diff/hw_target_check.py`**, run with `.venv-hw` Python:
  - both committed targets validate against the schema;
  - re-extracting each from its fake backend gives byte-identical JSON (the fake data is fixed in
    the package version);
  - the hash agrees.
- **`cqr hw capabilities`** on both targets: the expected modes, `snapshot hash ok`, exit 0. A
  target with a corrupted calibration number gives exit 1. A missing file gives exit 2.
- **CI.** A new step "Hardware target (Stage 24a)" in `scripts/ci_local.sh` and
  `.github/workflows/ci.yml`. Locally it uses `.venv-hw/Scripts/python.exe`, falling back to n/a
  with a reason if `.venv-hw` is absent (as the llvm step does). The pass mark becomes
  **20 PASS, 0 FAIL, 4 n/a** on this machine. In ci.yml the step installs from
  `hw/requirements.lock`; CI stays local, so ci.yml is kept consistent but not run.
- **Lean tests** (`tests/CQRVTests/HardwareTarget.lean`): `ofJson` on a small inline target, and
  `checkHash` on it.

### 24a Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry, with the versions, the two targets and the canonicalization choice;
- `docs/PROJECT_STATUS.md`;
- README: the status line, and one sentence on `hw/` and `.venv-hw`.

Acceptance:
- `lake build` green and warning-free;
- CI 20 PASS, 0 FAIL, 4 n/a;
- the two targets committed;
- the hash agreeing between Python and Lean.

Stop and ask in any of these cases:
- pip wants to download more than about 200 MB, or a package outside the dependency tree of the
  three;
- a fake backend's data is not deterministic across re-extraction;
- the canonical form cannot be made byte-identical between the two sides;
- the user declines the download (then stop; Track C is reconsidered).

---

## 24b — The lowering and the comparison on Aer (outline)

- `hw/lower.py`: the canonical circuit JSON → a Qiskit dynamic circuit (`if_test`, mid-circuit
  measure, bookkeeping for alloc / free).
- `tests/diff/hw_lower_check.py`: an ideal Aer simulation against the statevector reference,
  branch by branch (per classical assignment: the post-measurement state up to global phase, and
  the probability), on every committed example and generated instance with at most 6 data qubits.
- A new CI step; the pass mark becomes 21.

## 24c — Per-operation rates (outline)

- The per-operation-type rates from the snapshot.
- The weighted bound δ + Σ_types count · rate in the run reports (`cqr hw bound`, or an option of
  `cqr certify --target`), next to the old p̄ form.
- The Lean side computes the bound exactly from the rates in the target JSON.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests (with the pip versions and size for 24a),
(d) SORRIES.md, (e) open questions. Send it to the reviewer session (QUANTUM CODING) with
SendMessage, and print it.
