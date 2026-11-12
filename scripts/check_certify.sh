#!/usr/bin/env bash
# Stage 8b / 11b checks — report §3.3.2–3.3.3, §5.1.3, §8.4.1, §8.4.4, §9.5.1, §9.5.3 (`cqr certify`).
#
#   tests/diff/certify_check.py  cqr certify examples/grover_pred_037.cqr: status line, schema
#                                v1.3.0, grade, δ, axioms; circuit hash = SHA3 of the IR literal
#                                of Cert.lean (hashlib); .qasm / .qir re-parse to the literal;
#                                second run byte-identical (JSON except machine fields); the
#                                committed examples/certs/grover_pred_037 agrees; the XOR
#                                predicate tests/certify/xor_pred.cqr and the `if` predicate
#                                tests/certify/if_pred.cqr are certified (Stage 9a, 9a review);
#                                the second worked predicate examples/simple_alu_x0_1.cqr is
#                                certified and the committed certificates and run reports of
#                                both examples agree (Stage 9b);
#                                negative tests (network failing C.WF → kernel check fails,
#                                injected sorry → sorryAx, native_decide → its auxiliary axiom,
#                                search_while → Stage 4 hint); Stage 11b: without --profile
#                                certificate.json byte-identical to the committed one outside
#                                reference_configuration; --profile illustrative_sc: Grover
#                                and ALU fit all (tree, Stage 12a), δ_hw vacuous for both,
#                                `hardware` recomputed; Stage 12d: --shape few:log (grade
#                                (10, 172, 96, 2), diffusion_shape, the profile fits), the committed
#                                examples/certs/grover_pred_037_few, and a few:log Cert.lean
#                                with mcz_ok for a wrong n → kernel check fails (Stage 13a′:
#                                no per-instance classical step, grover_certificate_few_all);
#                                Stage 14a: schema v1.6.0 with solution_count {value, status};
#                                n ≤ 10 (default --count-limit, Stage 14c): status line `certified`, Cert.lean proves hM_count and
#                                `cert` has no hypothesis (kernel_decided); negative tests:
#                                grover_pred_037 --solutions 31 and simple_alu_x0_1 --solutions 29
#                                → solution_count_mismatch, nothing written; --count-limit 4 and
#                                --count-limit 0 → the conditional form (hM_card, hypothesis);
#                                (f′) Stage 14c: n = 11 without the flag → the conditional form;
#                                --profile ibm_kyiv → unknown profile listing illustrative_sc;
#                                Stage 15b: --uncompute coherent (schema v1.7.0, uncompute,
#                                grade (15, 200, 144, 7), no measurement; the profile fits with
#                                d = 200 = 200), the committed examples/certs/grover_pred_037_coh,
#                                --uncompute mbu byte-identical to Phase 1, few:log + coherent →
#                                unsupported_combination;
#                                Stage 16b: every Cert.lean carries prog / prog_scoped / net_ok /
#                                front_end between net and emitted and is byte-identical to the
#                                Stage 16a file (git 52ad73b) outside that block; schema v1.8.0
#                                with uncompute explicit and the proved front_end wording; run
#                                report row 1b kernel-checked;
#                                Stage 17b: schema v1.9.0 with grade_ext {two_qubit, t_depth,
#                                rot, meas, ff} = the emitted literal's counts and the G counts,
#                                gradeExt_eq right after grade_eq in every Cert.lean (the
#                                committed files = the 16b files, git 7f46857, + that theorem),
#                                the committed .qir / .qasm = the 16b files; measured grade_ext
#                                (126, 39, 0, 18, 36) / (137, 28, 0, 15, 30) /
#                                (106, 77, 0, 8, 16) / (216, 74, 0, 0, 0);
#                                Stage 20b3: the counting certificate (CertifyTool count-certify
#                                grover_pred_037 m = 4, schema v1.10.0 pattern Count, the
#                                committed examples/certs/grover_pred_037_count, the circuit hash
#                                by replaying the six block literals, QASM / QIR re-parse with
#                                decomposeCp, the composed grade (20, 1388, 660, 8) recomputed,
#                                two negative kernel tests)
#   tests/diff/profile_schema.py profiles/*.json against docs/profile.schema.json;
#                                illustrative_sc = report Table 3.5 / §3.3.3 (renamed from
#                                ibm_kyiv in Stage 14a, no alias); mutated profiles rejected by
#                                the schema and by `cqr certify --profile` (Stage 11b)
#
# Usage (after `lake build`, from anywhere):  scripts/check_certify.sh
#   PYTHON=.venv/Scripts/python.exe scripts/check_certify.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "check_certify: $CQR not found (run lake build first)" >&2; exit 2; }
"$PY" -I "$ROOT/tests/diff/profile_schema.py" --cqr "$CQR"
"$PY" -I "$ROOT/tests/diff/certify_check.py" --cqr "$CQR"
echo "check_certify: all checks passed"
