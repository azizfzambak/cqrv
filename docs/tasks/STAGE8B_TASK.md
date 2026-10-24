# Stage 8b — `cqr certify`: specialization, kernel check, axiom audit, honest status, benchmark

Report sections: §5.1.3 (per-request work = proof specialization + kernel checking), §8.4.1
(specializing π to concrete parameters), §8.4.4 (certificate contents), §9.5.1 (master
discipline: "certified" only when sorry-free and axiom-audited; reference configuration),
§9.5.3 (CI kernel-checks certificates; the sorryAx/axiom audit is blocking), §5.2.4
(`hM_card` is a hypothesis, never decided by enumeration).
Precondition: Stage 8a accepted. `git switch -c stage-8b main`; one commit; include this file
(untracked). Windows: `LEAN_NUM_THREADS=4`.

## The idea (reviewer)

The Grover lemma is proved once, parametrically. A request is certified by **generating a small
Lean file that instantiates it** at the requested network, n, M, r, and having the **Lean kernel
check that file** — never by re-proving (§5.1.3). The CLI only writes text and runs Lean; its
own code is not trusted for the claim. The emitted circuit must be **the circuit the proof is
about**: the certificate file itself fixes that link.

## Reviewer decisions (record in DECISIONS.md)

1. **Certificate file** `certs/<name>/Cert.lean` (git-ignored except for the Grover example
   committed under `examples/certs/grover_pred_037/`), importing `CQRV`, containing:
   the network literal produced by `toNetwork` of the request; `theorem cert : …` = the
   specialization of `grover_parametric_lemma` (via the `grover_pred_037_certified_statement`
   pattern of 7b) with `hM_card` as an explicit **hypothesis** of the theorem; side conditions
   (`synthesizeOracle … = .ok …`, `WF`, `DiffusionCert` for n, the computed grade, δ as an exact
   rational) discharged by `decide +kernel` / `rfl` — **never `native_decide`**; and a
   kernel-checked link `circuitHash (groverCircuit …) = "<hex>"` **or** an equality of the
   computed circuit with the IR literal, so the hash in the JSON is the hash of the proved
   circuit (choose the variant that kernel-checks in reasonable time; record it).
2. **Kernel check** = `lake env lean certs/<name>/Cert.lean` (exit code 0) followed by
   `#print axioms cert` in the same file; the CLI parses the output.
3. **`auditAxioms`**: passes iff the list ⊆ {`propext`, `Classical.choice`, `Quot.sound`} and
   contains no `sorryAx`; any other axiom must be listed in a named trust-boundary table
   (empty today) or the audit fails.
4. **Status words** (CLAUDE.md rule 10): print and write `"certified"` **only** if the kernel
   check succeeded and `auditAxioms` passed; the line must also state the hypotheses, e.g.
   `certified (conditional on: solution_count = 32)`. Otherwise
   `certificate with tracked obligations: <list>` (e.g. `lemma_6_3_2_xor` for an XOR predicate,
   or the failing axiom). Rejected: an unconditional "certified" while `hM_card` is a hypothesis.
5. **CI**: `print_axioms.sh` becomes **blocking** for theorems in `CQRV/Certify` and for the
   committed example certificate (Stage 0 promised this for Stage 8); CI runs `cqr certify
   examples/grover_pred_037.cqr` and validates the JSON against the schema.
6. **Benchmark** `scripts/bench_kernel.sh`: times the kernel check of the example certificate
   (median of 5 runs, excluding the first), prints CPU model, cores, clock if available, Lean
   version, Mathlib and Physlib revs; writes them into the certificate's
   `reference_configuration`. The report's 0.3 s is a target for a 3 GHz core (§9.5.1) — record
   the measured value, do not tune for it.

## Tasks

1. `CQRV/Certify/Generate.lean`: render the `Cert.lean` text for a matched Grover request.
2. `CQRV/Certify/Audit.lean`: run Lean, parse `#print axioms`, `auditAxioms`.
3. `cqr certify <file> [--solutions M] [--iterations r] [--out dir]`: check → extract → match →
   synthesize (r = r⋆ unless given) → generate → kernel-check → audit → write
   `certificate.json`, `<name>.qir`, `<name>.qasm` (8a emitters, from the **same** circuit) →
   print the status line (decision 4). Non-matching input → the Stage 4 hint, exit 1.
4. `scripts/bench_kernel.sh` (decision 6).
5. Commit `examples/certs/grover_pred_037/` (Cert.lean, certificate.json, .qir, .qasm).

## Tests / acceptance

- `cqr certify examples/grover_pred_037.cqr` → status
  `certified (conditional on: solution_count = 32)`, JSON valid, grade {15,230,72,7}, δ "7/128",
  axioms exactly the standard three, hashes reproducible on a second run (byte-identical JSON
  except timing fields).
- **Negative tests (must not say "certified")**: (a) an XOR predicate (Stage 5 corpus) →
  `tracked obligations: lemma_6_3_2_xor`; (b) a deliberately broken certificate file (inject a
  `sorry` in a temp copy) → audit fails with `sorryAx`; (c) `search_while` → hint, exit 1.
- `bench_kernel.sh` output pasted in the closing reply.
- `lake build` green, all previous checks green; CI updated (decision 5).

## Stop conditions

- The specialized certificate does not kernel-check without `native_decide` within ~10 minutes
  locally → stop and report which side condition is slow.
- The emitted circuit's hash cannot be tied to the proved circuit inside the checked file → stop
  and propose; do not fall back to "trust the CLI".
- Do not start Stage 9 (second predicate, run report).

## Closing reply

CLAUDE.md format, under 40 lines; in (e): the measured kernel-check time with CPU, the hash-link
variant chosen, the three negative-test outputs, and the exact status line printed.
