# Stage 8a — SHA3-256, certificate record and JSON schema, QIR / OpenQASM 3 emitters

Report sections: §5.3.1–5.3.4 (trust layers; emitted IR as explicit trust boundary), §8.4.2
(certificate structure), §8.4.3 (QIR export, Adaptive Profile, project-level callees lowered to
`__quantum__qis__*`), §8.4.4 (certificate contents), §9.5.1 (no `sorry`, reference configuration
recorded), §9.5.3 (JSON envelope: proof-term hash, grade, trust boundary, QIR profile,
hardware-perturbation conjunct, predicate and circuit hashes), §3.3.3 (δ_hw = δ + G·p̄).
Precondition: Stage 7b accepted (main = 7b review commit). `git switch -c stage-8a main`; one
commit; include this file (untracked). Windows: `LEAN_NUM_THREADS=4`; Python `.venv`.
**Engineering stage, no new proofs.** Stage 8b (next task) wires `cqr certify` with kernel
checking and the axiom audit; 8a builds the parts.

## Reviewer decisions (record in DECISIONS.md)

1. **SHA3-256 in Lean** (DECISIONS 2026-10-21): Keccak-f[1600] + SHA3 padding (`0x06 … 0x80`),
   rate 136 bytes, on `ByteArray`. Python `hashlib.sha3_256` is used **only as a test oracle**.
   Test vectors (from Python, checked by the reviewer): `""` →
   `a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a`, `"abc"` →
   `3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532`; plus a differential test
   on 200 random byte strings of lengths 0–600 (crossing the 136-byte block boundary).
2. **What is hashed.** `predicate_hash` = SHA3 of the DSL source text after normalizing line
   endings to LF; `circuit_hash` = SHA3 of the canonical IR JSON (`Circuit.toJson`, compact,
   keys sorted); `proof_hash` = SHA3 of the generated certificate `.lean` file (8b) together
   with the `lean-toolchain` line and the Mathlib/Physlib revs from `lake-manifest.json`
   (concatenated with a fixed separator — document it). Rejected: hashing `.olean` files
   (toolchain-internal, not stable across platforms).
3. **Certificate JSON schema v1.0.0** (semver, field `schema_version`). Fields: `pattern`,
   `instance` (n, M, r), `spec` (ε = "0", δ as exact rational string, e.g. "7/128",
   `success_probability` "121/128"), `grade` {w,d,t,a} (measured), `hypotheses` (list, e.g.
   `"solution_count = 32 (hM_card, supplied, not decided)"`), `restoration`
   ("AncRestore: all ancillae |0…0⟩ on density operators"), `hashes` {predicate, circuit,
   proof}, `trust_boundary` {emitted: "QIR text", profile: "adaptive_profile", emitter:
   "unverified; translation-validated by re-parse"}, `hardware_perturbation`
   {formula: "δ_hw ≤ δ + G·p̄", G: gate count from the IR, p̄: "profile parameter"},
   `reference_configuration` {lean, mathlib, physlib, cpu (8b fills)}, `axioms` (list, 8b fills),
   `status` ("certified" | "certificate with tracked obligations" — 8b decides).
   Ship `docs/certificate.schema.json` (JSON Schema draft 2020-12) and validate against it in
   the Python tests (`jsonschema` pinned in `tests/diff/requirements.txt`).
4. **QIR Adaptive Profile, static qubit addressing.** Emit LLVM IR text with opaque pointers:
   qubits `inttoptr (i64 k to ptr)` (data 0..n−1, then ancillae), results likewise; gates as
   `__quantum__qis__{h,s,s__adj,t,t__adj,x,z,cnot,cz}__body`; `measure → c` as
   `__quantum__qis__mz__body(ptr q, ptr r)`; `ifBit c g` as
   `__quantum__qis__read_result__body(ptr r)` + `br i1` to a block with `g`; entry point with
   attributes `"entry_point" "qir_profiles"="adaptive_profile" "required_num_qubits"="…"
   "required_num_results"="…" "output_labeling_schema"`; module flags `qir_major_version`,
   `qir_minor_version`, `dynamic_qubit_management` false, `dynamic_result_management` false.
   The report's listing uses project-level callees (`@temp_logical_and`, `@grover_diffusion`);
   emit them as defined functions lowered to QIS intrinsics (§8.4.3) **or** emit the flat gate
   list — choose, record, and keep the terminal measurement once at the end
   (`measure_all` over the data register, record output labels). Rejected: dynamic
   `%Array*` allocation (not in the Adaptive Profile's static-addressing model).
5. **OpenQASM 3**: `OPENQASM 3.0; include "stdgates.inc"; qubit[n] x; qubit[a] anc; bit[m] c;
   bit[n] out;` gates by name, `c[j] = measure q;`, `if (c[j]) { … }`, final
   `out = measure x;`.
6. **Translation validation (the emitter stays a trust boundary).** A Python re-parser reads the
   emitted QIR and QASM back into the IR JSON format and the test asserts **exact equality** with
   the Lean IR (gate by gate, qubits, bits, conditions). Additionally, the re-parsed QASM of the
   Grover oracle is simulated with the Stage 5 harness (all branches, random superpositions).
   If `llvm-as` is available (CI: install `llvm` via apt), the QIR text must assemble; locally
   the check is skipped with a message, never silently.

## Tasks

1. `CQRV/Certify/SHA3.lean` (decision 1) with tests (Lean `#guard` for the two vectors, Python
   differential).
2. `CQRV/Certify/Certificate.lean`: `structure Certificate` (decision 3), `toJson`, and a
   builder from (source text, extracted signature, match, circuit, grade, r, n, M, exact δ).
   The exact δ for the Grover pattern: compute `sin²((2r+1)θ)` as a rational from `s = M/2ⁿ`
   via the Chebyshev recurrence (`sin((2r+1)θ) = sin θ · U_{2r}(cos θ)`, so the square is a
   polynomial in s) — implement with `Rat`, test r = 2, s = 1/8 → 121/128.
3. `CQRV/Emit/QIR.lean`, `CQRV/Emit/QASM.lean` (decisions 4, 5).
4. CLI: `cqr emit <file> --format qir|qasm [--iterations r] [--solutions M]` (Grover circuit of the
   matched instance), printing to stdout.
5. `tests/diff/`: `reparse_qir.py`, `reparse_qasm.py`, schema validation, SHA3 differential; a
   driver in `scripts/` run by CI (with `llvm-as` in CI).

## Tests / acceptance

- `lake build` green, all previous checks green (oracle JSON byte-identical, harnesses).
- SHA3: both vectors + 200 random strings match Python.
- QIR and QASM of `grover_pred_037` (r = 2) re-parse to exactly the Lean IR; the QASM oracle
  simulates correctly in every branch; `llvm-as` passes in CI.
- `cqr emit … --format qir` contains `"qir_profiles"="adaptive_profile"`, `required_num_qubits`
  = 15, and exactly one terminal measurement block over the 8 data qubits.
- A sample certificate JSON (built by a Lean test or a CLI dry-run without kernel check) validates
  against the schema, with δ "7/128", grade {15,230,72,7}, `status` left as
  `"not yet audited"` (8b sets it).

## Stop conditions

- The re-parsed IR differs from the Lean IR → stop and report the first differing gate (emitter bug).
- The Adaptive Profile cannot express `ifBit` with static results as above → stop and propose.
- Do not generate or kernel-check certificate `.lean` files, do not change `print_axioms.sh` to
  blocking, do not print the word "certified" anywhere — all of that is 8b.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): the QIR choice of decision 4 (callees vs flat), any
schema field you had to add or rename, and whether `llvm-as` ran.
