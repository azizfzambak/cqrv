#!/usr/bin/env bash
# Second worked predicate — report §8.5.3, Table 9.2; §6.2.4, §8.2 (Stage 9b, decisions 2, 3).
#
# Runs tests/diff/benchmark_diff.py against the built `cqr` executable on
# examples/simple_alu_x0_1.cqr (RevLib Simple ALU, bit 1 of x0): reference from the SyReC
# semantics, M by enumeration (test oracle only), check / extract / match / synthesize, the
# oracle, one Grover iteration and the full Grover circuit in every measurement branch, success
# probability = sin^2((2r*+1) theta) = 1 - delta exactly. Runtime ~4 min.
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
