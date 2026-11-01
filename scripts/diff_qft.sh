#!/usr/bin/env bash
# Differential test of the QFT / approximate QFT circuits — PHASE2_SPEC.md §A.2 (Stage 18b B4);
# CLAUDE.md rule 9. `qft_basis` is proved in Lean (CQRV/Circuit/QFTCorrect.lean); this is the
# independent numerical check of the circuits and of the Stage 18c AQFT bounds.
#
# Runs tests/diff/qft_diff.py: the circuits come from `lake env lean --run
# scripts/CertifyTool.lean qft-sample --all 6` (one Lean start); for m = 1..6 the simulated
# `qftCircuit m` equals R·F (qubit 0 the most significant bit, as `qft_basis`), is unitary, its
# `adjointGates` is the inverse, and for kmax = 1..m the spectral distance to `aqftCircuit m kmax`
# is below both 2π m / 2^kmax and the sum of the dropped angles; negative control: one rotation's
# sign flipped is detected.
#
# Usage (after `lake build`):  scripts/diff_qft.sh [--m-max 6] [--seed S]
#   PYTHON=.venv/Scripts/python.exe scripts/diff_qft.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
cd "$ROOT"
"$PY" -I "$ROOT/tests/diff/qft_diff.py" "$@"
