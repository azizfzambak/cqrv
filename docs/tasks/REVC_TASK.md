# Revision task C — R12: two or three combinational benchmarks

Written 2026-11-16 by the reviewer session (author's decision of 2026-11-16; `docs/REVIEW_RESPONSE_1.md`
§4, R12). Runs after task B is accepted. Branch `rev-c` from `main` at `90a1b3e` (the rev-b review
commit). This file goes into the first commit. The new certificates follow task B's formats
(schema 1.12.0, `hashes.library` current; `libhash.py --release` passes at the end).

**Why.** Both reviews say the evidence rests on too few predicates: a 3-literal conjunction
(`grover_pred_037`), one RevLib bit (`simple_alu_x0_1`), and the small frontier family. This task
adds two or three predicates with real arithmetic structure, certified end to end by the existing
tools. **No new Lean theory**: if a benchmark needs a new theorem or a new pattern, it is out of
scope; report it instead.

## The benchmarks (write each from its mathematical definition; no download)

1. **Comparator** `cmp4`: x > y for 4-bit x, y (n = 8 inputs, M = 120). Through a bounded fold or
   an explicit borrow chain, whichever the DSL expresses more naturally.
2. **Adder check** `addchk3`: x + y ≡ z (mod 8) for 3-bit x, y, z (n = 9, M = 64). A ripple-carry
   sum compared bit by bit.
3. **Weight function** `wt8_3`: exactly three of eight bits set (n = 8, M = 56). A small counter
   in a fold. (This is the shape of the RevLib weight functions rd53 / rd73 / rd84; cite them by name
   in the file header as the family, not as a transcribed file.)

If one of them makes M/N too large for a useful Grover iteration count, or the DSL cannot express
it without a new construct, replace it with the nearest variant (for example x ≥ y + 5, or a
different weight) and say why. Two benchmarks are enough if the third hits a guard.

## For each benchmark

1. `examples/<name>.cqr` with a header: the definition, the input layout (bit 0 = LSB), and the
   value of M computed independently (a short Python enumeration in the check script, not by hand).
2. The statevector harness passes on the synthesized circuit (all branches; n ≤ 12), for the
   default shape and for `--shape few:log`, before any grade is claimed (CLAUDE.md rule 9).
3. `cqr certify` with the default shape → `examples/certs/<name>/` (Cert.lean, certificate.json,
   .qasm, .qir, run_report), the count kernel-decided (n ≤ 10), standard three axioms.
4. For **one** of them (the comparator unless it hits a guard), also `--problem count --precision 4`
   → `examples/certs/<name>_count/`: a counting certificate with the compositional grade bound and
   its block accounting.
5. Register the new certificates wherever the existing ones are re-certified and checked
   (`scripts/ci_local.sh` lists, `tests/diff/certify_check.py`), so that CI re-certifies them byte
   for byte. No new CI step.
6. Hardware artifacts are **not** required. Do not transpile unless a single artifact for the
   smallest benchmark is cheap (check file ≤ 4 GB, ≤ 60 s); if you do, it is optional and goes
   through the existing tools unchanged.

## Report table

One row per certificate: n, M, r, success probability, δ (exact), grade (w, d, t, a) and
`GradeExt`, the circuit's gate count, kernel time (single run; R11 will re-measure) and peak
memory. Add the same rows to `docs/M5_REPORT.md` §1 as a dated "revision R12" addition.

## Guards

- any certificate whose kernel check exceeds 300 s or 8 GB (try `--shape few:log` once, then report);
- a harness failure (stop: a synthesis bug is a finding, not something to work around);
- a predicate the DSL cannot express;
- about 600 hand-written lines (most of this task is examples and lists).

## Acceptance

`lake build` green, 0 warnings, 0 `sorry`; the new certificates regenerate byte for byte; the
affected `tests/diff` checks run once by you (one Lean process at a time); the reviewer runs the CI
(pass mark 26 / 4 n/a). `docs/DECISIONS.md` entries for every substitution. The usual report.
