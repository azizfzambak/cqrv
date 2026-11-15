# Stage 24 — Target model and lowering (PHASE2_SPEC §C.1; Track C, Paper 1)

PHASE2_SPEC.md §C, §C.1. Report: §3.1.3, §5.3. PHASE2_ROADMAP row 24. Written at the M4 review
(2026-11-15) by the reviewer, under the author's delegation.

Stage 24 has three tasks, one commit each:
- **24a**, the environment, the target model and `cqr hw capabilities`, is specified here;
- **24b**, the lowering and the comparison on Aer, is specified below (written at the 24a review);
- **24c**, the per-operation rates, is specified below (written at the 24b review).

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

## 24b — The lowering and the comparison on Aer (written at the 24a review, 2026-11-15)

PHASE2_SPEC §C.1 "Lowering", and the "24a done" paragraph. Precondition: main = the 24a review
commit. Start with `git switch -c stage-24b main`. The invariants of Stage 24 hold. No new
download: everything needed is in `.venv-hw` and `.venv`.

### S1. `hw/lower.py`

**`lower(circuit_json) -> QuantumCircuit`.** The input is the canonical circuit JSON of
`Circuit.toJson`: `n_data`, `n_anc`, and gates with `op`, `q`, `c`, `a`, `k`, `if`. The circuit
has n_data + n_anc qubits, in the JSON's flat order, and one classical register of nBits bits.
The mapping:

| IR | Qiskit |
|---|---|
| `h s sdg t tdg x z` | the same gates |
| `cnot` | `cx` |
| `cz` | `cz` |
| `p a k` | `p(2πa/2^k)` |
| `cp a k` | `cp(2πa/2^k)` |
| `measure q → c` | `measure(q, c)` |
| `if: k` | `with qc.if_test((clbit k, 1)): <the gate>` |
| `alloc`, `free` | nothing (bookkeeping) |

The phase convention must match the IR's: `p` multiplies |1⟩ by exp(2πi a/2^k), Qiskit's phase
gate. Check it numerically on one gate.

**CLI.** `python -I hw/lower.py <circuit.json> [--qasm-out f]`. The QASM export of the lowered
circuit is for inspection only; the comparison is on the circuit object.

### S2. The branch-by-branch comparison (`tests/diff/hw_lower_check.py`, `.venv-hw` Python)

- For each instance and each assignment c of the classical bits that occurs with nonzero
  probability, compare the reference and Aer on two things:
  - the branch probability p_c, to 1e-9;
  - the normalized post-measurement state of the branch, up to global phase, to 1e-9 in
    fidelity.
- **The reference** is the in-repo statevector harness (`tests/diff/statevector.py`, which
  already enumerates branches).
- **The Aer side** uses Aer's own dynamic-circuit execution, not a hand evolution with Qiskit
  operators. Find the exact per-branch mechanism in the installed qiskit-aer 0.18.2, for example
  `save_statevector` / `save_density_matrix` with `conditional=True`, or
  `save_probabilities_dict`, and say which you used.
  - If Aer gives no exact per-branch data, compare instead the exact output density matrix of
    the whole channel (`save_density_matrix`, ideal), plus the branch probabilities from Aer's
    exact probabilities. Report that this is the weaker check.
- **Instances.** Every one whose data register is at most 6 qubits:
  - the MBU gadget (`mbuCircuit`), and its uncorrected variant;
  - the Grover circuits of every `examples/*.cqr` with n ≤ 6 that `cqr synthesize --grover`
    accepts, in both uncomputation modes and with the few:log diffusion where it applies, among
    them `simple_alu_x0_1`;
  - one counting circuit with n = 4, m = 2, through CertifyTool `counting-sample`'s IR JSON or
    `cqr`, which exercises `p` / `cp`;
  - the 23a and 23b gadgets that are circuits (the parity instance, the dirty gadget).
- **Inputs.** The all-zero input. For the oracle-level instances, also every computational-basis
  data input (prepend X gates); state the count.

### S3. The schema check moves to `jsonschema`

`scripts/check_hw_target.sh` runs the schema validation of the two targets with `$PYTHON` (`.venv`,
which has `jsonschema` 4.26.0). `.venv-hw` keeps the rest of `hw_target_check.py`. The built-in
subset validator is removed, or kept only as a documented fallback that CI does not use.

### S4. CI

A new step "Hardware lowering (Stage 24b)" in `scripts/ci_local.sh` and `.github/workflows/ci.yml`:
`scripts/check_hw_lower.sh`, using `.venv-hw`, and n/a with a reason if it is absent. The pass
mark becomes **21 PASS, 0 FAIL, 4 n/a**. Report the step's time; above 300 s, stop and say what
takes the time.

### 24b Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry, with the Aer mechanism used and the instance count;
- `docs/PROJECT_STATUS.md`;
- README's status line.

Acceptance:
- `lake build` green (no Lean change is expected);
- CI 21 PASS, 0 FAIL, 4 n/a;
- every instance agreeing on every branch.

Stop and ask in any of these cases:
- an instance disagrees on a branch: report the instance, the branch and both values, and do not
  "fix" the reference;
- Aer's dynamic-circuit execution does not support a construct the IR emits;
- a new download would be needed.

## 24c — Per-operation rates and the weighted bound (written at the 24b review, 2026-11-15)

PHASE2_SPEC §C.1 "Per-operation rates", the "24b done" paragraph and its refinement.
Precondition: main = the 24b review commit. Start with `git switch -c stage-24c main`. The
invariants of Stage 24 hold, and there is no new download. The committed certificates and their
JSONs are unchanged; the old p̄ form of Stage 11b stays as it is.

### T1. The decomposition table and the counts (Lean, `CQRV/Hardware/Bound.lean`, Physlib-free)

- **`basisCounts (basis : TargetBasis) (C : Circuit) : BasisCounts`.** It counts, per basis
  operation, what the circuit becomes under the table of the refinement:
  - one-qubit basis gates by name;
  - two-qubit basis gates;
  - mid-circuit measurements and final measurements.

  A `measure` is mid-circuit when a gate follows it on any qubit or under its bit; otherwise it
  is final. A conditioned gate counts as executed. `alloc` and `free` count nothing.
- **`TargetBasis`.** `cz` or `cx`, read from the target's `basis_gates`. A target whose basis is
  neither is an error with a message.

### T2. The rates and the bound

- **Decimal reader.** `calibration` numbers are decimal strings. Read them exactly into ℚ, reusing
  or generalizing the decimal reader of `CQRV.Certify.Profile` for p̄.
- **The rate of each basis operation**, over the device:
  - **worst:** the maximum over its qubits or edges, a sound bound for any layout;
  - **median:** labelled "typical, not a bound".

  Readout is the maximum or median over the qubits. The mid-circuit rate is absent from the
  snapshot, so it is the readout rate as a labelled assumption, and its coefficient is reported
  separately.
- **`weightedBound`.** δ_hw ≤ δ + Σ_types count · rate, exact in ℚ for the worst-case form; the
  median form is printed alongside.
- **The CLI.** `cqr hw bound <file.cqr> --target <t.json> [--solutions M] [--iterations r]
  [--shape tree|few:log] [--uncompute mbu|coherent] [--json]`.
  - It builds the Grover circuit as `cqr certify` does, by the same `groverInstance`, and uses δ
    from `groverDelta`.
  - It refuses `--uncompute mbu` on a target without feed-forward: exit 2, "mbu needs
    feed-forward; the target supports coherent only".
  - It prints the counts per basis operation, the rates (worst and median), each product, the
    sum, δ, the worst-case δ_hw (marked vacuous when ≥ 1), the median figure with its label, and
    the coefficient of η_mid.
  - It never writes a certificate, and its output says "reported, not certified (Stage 27)".

### T3. Checks

- **`tests/diff/hw_bound_check.py`.** An independent Python recomputation, from the circuit JSON
  and the target JSON, of the counts, the rates (worst, median) and both bound figures, for:
  - the committed Grover examples (grover_pred_037 tree mbu, tree coherent and few:log;
    simple_alu_x0_1);
  - against both targets, with mbu only on FakeTorino.

  The figures must agree exactly with `cqr hw bound --json` (rationals as fractions; floats only
  in the median line).
- **Python only:** the transpiled count of Qiskit for the same circuits against the target (one
  seeded transpile with optimization level 0) is printed next to the table counts, for
  information, not compared. It shows how far the table is from the transpiler before Stage 25.
- **CI.** The checks join the step "Hardware target" (no new step); the pass mark stays 21.
- **Lean tests:** `basisCounts` on the MBU gadget for both bases; `weightedBound` on a tiny
  target.

### 24c Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry, with the table, the aggregation, the mid-circuit assumption and the
  numbers for the committed examples;
- `docs/PROJECT_STATUS.md`;
- README's status line.

Acceptance:
- `lake build` green and warning-free;
- CI 21 PASS, 0 FAIL, 4 n/a;
- the bound figures reported for every committed example and target, with vacuity marked.

Stop and ask in any of these cases:
- a fake's calibration has a rate that cannot be read exactly;
- a statement of mine is false.

Report in (e), without stopping, every example where the table count and the transpiled count
differ by a factor above 3. Routing SWAPs are expected to cause this; it informs Stage 25.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests (with the pip versions and size for 24a),
(d) SORRIES.md, (e) open questions. Send it to the reviewer session (QUANTUM CODING) with
SendMessage, and print it.
