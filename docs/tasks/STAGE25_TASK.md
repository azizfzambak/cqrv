# Stage 25 — Transpile with a witness, noisy simulation, run reports (PHASE2_SPEC §C.2; Track C)

PHASE2_SPEC.md §C.2. Report: §5.3, §3.1.3. PHASE2_ROADMAP row 25. Written at the 24c review
(2026-11-15) by the reviewer, under the author's delegation.

Stage 25 has two tasks, one commit each:
- **25a**, the witness, the artifact and the bound on the physical circuit, is specified here;
- **25b**, the noisy runs and the reports, is specified below (written at the 25a review).

Precondition: main = the 24c review commit. Start with `git switch -c stage-25a main`.

**Invariants of Stage 25** (as Stage 24):
- No Lean statement changes, no certificate is regenerated, and the outputs of the existing `cqr`
  subcommands are byte-identical.
- The `cqr` closure stays Lean core + Mathlib.
- `.venv` and its lock are untouched.
- No new download.
- No network.
- Check Qiskit APIs in the installed version.
- The transpiler and Aer are untrusted: every claim about their output is a check of that output,
  never an assumption.

---

## 25a — The witness, the artifact, the bound on the physical circuit

### U1. Our basis translation (`hw/decomp.py`)

- **The table.** An explicit decomposition table for the cz basis (Torino) and the cx basis
  (Washington): every IR gate h, s, sdg, t, tdg, x, z, p, cnot, cz, cp (a k) and a `swap` entry
  to a list of basis gates (rz with an exact angle, sx, x, cz / cx).
  - **One global phase per entry**, recorded with it. Each entry is checked numerically: the
    product of the basis matrices equals the IR gate's matrix times the recorded phase, to
    1e-12. Stage 26 proves the entries in Lean.
  - **Conditioned gates.** Each basis gate of the translation keeps the condition, so an
    `if_test` body holds the basis sequence.
- **`translate(circuit_json, basis) -> (QuantumCircuit, provenance)`.** The provenance is, per
  basis gate, the index of the IR gate it came from and its table entry.

### U2. Layout and routing (`hw/transpile.py`)

- **The passes.** Seeded layout and routing on the translated circuit against the fake backend's
  coupling map, with no optimization and no further basis translation. Find, in Qiskit 2.6.2,
  passes that support control flow (`if_test` blocks) and keep the inserted SWAPs as `swap`
  gates (for example SabreLayout and SabreSwap in a custom PassManager). Say which you used.
- **Afterwards:** decompose the SWAPs by the table entry, and extract the witness of
  PHASE2_SPEC §C.2:
  - the initial layout and the final layout;
  - each SWAP with its position (the index in the translated gate list it precedes) and its
    physical edge;
  - the table entries used;
  - the classical-bit map;
  - the seed;
  - the versions.
- **Schema** `docs/hw_witness.schema.json`, version 1.0.0.
- **`reconstruct(translated, witness) -> physical`**, deterministic. The check:
  - `reconstruct(...) == physical` gate for gate;
  - every two-qubit gate on a coupling edge;
  - measurements and `if_test` blocks preserved, with bits mapped by the witness.

### U3. The bound on the physical circuit and the seed search

- **The physical counts** per basis operation, per used qubit or edge, come from the physical
  circuit, with a conditioned gate counted as executed.
- **The rates** per used qubit or edge come from the target's calibration, read exactly (decimal
  strings as Fractions).
- **The bound.** δ_hw ≤ δ + Σ_ops rate, in exact Fractions, with the n data readouts and the
  mid-circuit readout assumption of 24c.
- **The seed search.** A fixed list of seeds, for example 0 … 19. For each seed, record whether
  the layout uses an error-1.0 edge, and its bound. Choose the seed with the least bound. The
  report lists all seeds tried.

### U4. The artifact (`hw/artifact.py`)

`PhysicalArtifact` JSON, schema `docs/hw_artifact.schema.json` 1.0.0:
- the hashes of the certificate JSON (if the instance comes from a committed certificate), the
  logical circuit JSON, the target snapshot, the witness and the physical circuit's QASM 3;
- the versions, the seed, the bound figures and the counts.

Write the artifacts of the instances of U5 under `hw/artifacts/<instance>__<target>/`: the witness
JSON, the physical QASM 3 and the manifest. Commit them if their total size is under about 5 MB;
otherwise commit only the manifests and say so.

### U5. Instances and checks (`tests/diff/hw_transpile_check.py`)

**Instances:**
- the MBU gadget;
- Grover with n = 2 and n = 3: two small predicates, written as `examples/hw_n2.cqr` and
  `examples/hw_n3.cqr` if no existing example has those sizes;
- `grover_pred_037` (tree mbu, tree coherent, few:log mbu) and `simple_alu_x0_1` (the same three);
- each on FakeTorino, and the coherent ones also on FakeWashingtonV2.

**Checks:**
- the table entries numerically;
- the reconstruction equality;
- the coupling edges;
- the schemas, with `.venv`'s `jsonschema`;
- the manifest hashes recomputed;
- the bound recomputed;
- the seed search deterministic (the same choice twice).

**Ideal-equivalence check** for the instances with at most about 20 physical qubits used: the
ideal Aer simulation of the physical circuit, with the final layout undone, agrees with the
logical circuit's branch by branch, as in 24b. This checks that routing preserved the semantics.

**CI.** A new step "Hardware transpile (Stage 25a)"; the pass mark becomes **22 PASS, 0 FAIL,
4 n/a**. Report the step time; above 300 s, keep the full set out of CI and give the CI subset.

### 25a Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry, with the passes, the table, the seed list and the bound table;
- `docs/PROJECT_STATUS.md`;
- README's status line;
- `hw/README.md` (the pipeline).

Acceptance:
- `lake build` green, with no Lean change expected;
- CI 22 PASS, 0 FAIL, 4 n/a;
- every reconstruction exact;
- the bound table for every instance, with vacuity marked.

Stop and ask in any of these cases:
- no Qiskit pass both supports control flow and keeps SWAPs (report the alternatives);
- a reconstruction differs;
- the ideal-equivalence check disagrees on a branch;
- a new download would be needed.

---

## 25b — Noisy runs and run reports (written at the 25a review, 2026-11-15)

PHASE2_SPEC §C.2 "The runs", and the "25a done" paragraph. Precondition: main = the 25a review
commit. Start with `git switch -c stage-25b main`. The invariants of Stage 25 hold.

### V1. `hw/run.py --sim`

`python -I hw/run.py --sim <artifact dir> --shots N --seed s [--json out]`.
- **The circuit.** Load the committed `physical.qasm` and `manifest.json`. Reduce the circuit to
  its used qubits with the compact mapping of 25a's equivalence check, factored out into a shared
  helper. Append the readout of the n data qubits at `manifest.layout.data_physical`, into a new
  classical register; the IR has no final readout.
- **The noise model.** The fake backend's noise model (`AerSimulator.from_backend`, or
  `NoiseModel.from_backend` restricted to the used qubits), with the qubit mapping checked.
  Mid-circuit measurements get the fake's readout error; this is the labelled assumption of 24c,
  stated in the report.
- **The success predicate**, per instance:
  - **Grover instances:** P(x) on the data readout, where P is the instance's predicate.
  - **The MBU gadget:** it computes a phase, which a computational-basis readout cannot see. The
    run wraps it: prepare |++⟩ on the data, apply the gadget, then apply the inverse of the ideal
    output's preparation (H on data 1, CNOT data 0 → data 1, H on data 0, so that CZ|++⟩ goes to
    |00⟩). Measure the data and the ancilla. Success is the all-zero outcome. Build the wrapped
    gadget as a logical circuit and send it through 25a's pipeline as its own artifact
    (`mbu_gadget_wrapped`), so that the wrapper's two-qubit gate is routed too. Do not add gates
    after routing. State the wrapper in the report.
- **The run report** (JSON, plus Markdown with `--md`):
  - the manifest hash, the target snapshot hash, the seed, the shots, and the qiskit / aer
    versions;
  - the counts on the readout, and p̂ = successes / shots;
  - the two-sided 95 % Clopper–Pearson interval and the one-sided 95 % lower bound;
  - the ideal success probability (Aer without noise on the same compact circuit) and the
    reference (1 − δ, or 1 for the gadget);
  - δ_hw from the manifest;
  - the one-sided check p̂ ≥ 1 − δ_hw − √(ln(1/α) / (2 · shots)), at α = 0.05: "passes",
    "fails" or "vacuous (δ_hw ≥ 1)".

  The wording is "emulator run on the fake backend's noise model". It never says "verified on
  hardware" and never claims that the run validates the certificate.

### V2. The full set and the committed report

- `scripts/hw_runs.sh` runs every artifact of 25a at a fixed seed with 4 000 shots (or a smaller
  count if a run takes more than about 60 s; say which).
- It writes `docs/hw_runs/RUNS.md` (one table: instance, target, δ, δ_hw, ideal, p̂, interval,
  check) and the per-run JSONs under `docs/hw_runs/`. Commit them.
- Comment on the table in `docs/hw_runs/RUNS.md` in a few sentences: where the noisy p̂ sits
  relative to the bound and to the ideal, and which instances the bound covers.

### V3. Checks and CI

- **`tests/diff/hw_run_check.py`:**
  - the run report schema (`docs/hw_run.schema.json` 1.0.0, validated with `.venv`'s
    `jsonschema`);
  - the noiseless run equals the ideal probability to within the shot noise (a 5-sigma binomial
    tolerance);
  - the Clopper–Pearson figures recomputed;
  - the check's arithmetic recomputed;
  - the manifest hash link;
  - determinism: the same seed gives the same counts.
- **The CI subset:** the MBU gadget, hw_n2 and hw_n3 on FakeTorino, at 2 000 shots, in a new step
  "Hardware runs (Stage 25b)". The pass mark becomes **23 PASS, 0 FAIL, 4 n/a**. Report the step
  time; above 300 s, lower the shots and say so.

### 25b Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry, with the noise model, the wrapper, the shots and the table summary;
- `docs/PROJECT_STATUS.md`;
- README's status line;
- `hw/README.md`.

Acceptance:
- CI 23 PASS, 0 FAIL, 4 n/a;
- `docs/hw_runs/RUNS.md` committed;
- every non-vacuous check's outcome reported as it is. A "fails" is a finding, not something to
  fix.

Stop and ask in any of these cases:
- the noise model cannot be mapped to the compact circuit faithfully;
- a noiseless run disagrees with the ideal beyond the shot noise;
- a run of the CI subset takes more than about 120 s.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests, (d) SORRIES.md, (e) open questions. Send it
to the reviewer session (QUANTUM CODING) with SendMessage, and print it.
