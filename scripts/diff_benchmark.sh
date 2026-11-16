#!/usr/bin/env bash
# Worked predicates — report §8.5.3, Table 9.2; §6.2.4, §8.2 (Stage 9b, decisions 2, 3; revision R12).
#
# Runs tests/diff/benchmark_diff.py against the built `cqr` executable on
# examples/simple_alu_x0_1.cqr (RevLib Simple ALU, bit 1 of x0): reference from the SyReC
# semantics, M by enumeration (test oracle only), check / extract / match / synthesize, the
# oracle in every measurement branch, one Grover iteration and the full Grover circuit on 512
# fixed-seed sampled branches (`--all-branches`: every branch, ~45 min), success
# probability = sin^2((2r*+1) theta) = 1 - delta exactly. Runtime a few minutes.
#
# Since R12 (REVIEW_RESPONSE_1 §4; docs/tasks/REVC_TASK.md) it also runs tests/diff/r12_predicates.py:
# the benchmarks cmp4, addchk3, wt8_3 (harness on sampled branches, both shapes; the committed
# certificates addchk3, wt8_3 and wt8_3_count re-certified byte for byte; cmp4 is harness evidence only).
#
# Usage (after `lake build`):  scripts/diff_benchmark.sh [--seed S]
#   PYTHON=.venv/Scripts/python.exe scripts/diff_benchmark.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "diff_benchmark: $CQR not found (run lake build first)" >&2; exit 2; }
"$PY" -I "$ROOT/tests/diff/benchmark_diff.py" --cqr "$CQR" "$@"
# Revision R12 (docs/tasks/REVC_TASK.md): the benchmarks cmp4, addchk3, wt8_3 — reference semantics, the
# statevector harness (sampled branches, both shapes) and the byte-for-byte re-certification of
# examples/certs/{addchk3, wt8_3, wt8_3_count} (cmp4: harness evidence only); `R12_SAMPLE` branches per check (default 4)
"$PY" -I "$ROOT/tests/diff/r12_predicates.py" --cqr "$CQR" --sample "${R12_SAMPLE:-4}"
