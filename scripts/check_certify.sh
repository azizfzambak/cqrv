#!/usr/bin/env bash
# Stage 8b / 11b checks — report §3.3.2–3.3.3, §5.1.3, §8.4.1, §8.4.4, §9.5.1, §9.5.3 (`cqr certify`).
#
#   tests/diff/certify_check.py  cqr certify examples/grover_pred_037.cqr: status line, schema
#                                v1.3.0, grade, δ, axioms; circuit hash = SHA3 of the IR literal
#                                of Cert.lean (hashlib); .qasm / .qir re-parse to the literal;
#                                second run byte-identical (JSON except kernel_check); the
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
#                                reference_configuration; --profile ibm_kyiv: Grover exceeds
#                                depth, ALU fits all, δ_hw vacuous for both, `hardware` recomputed
#   tests/diff/profile_schema.py profiles/*.json against docs/profile.schema.json; ibm_kyiv =
#                                report Table 3.5 / §3.3.3; mutated profiles rejected by the
#                                schema and by `cqr certify --profile` (Stage 11b)
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
