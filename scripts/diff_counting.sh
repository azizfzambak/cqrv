#!/usr/bin/env bash
# Differential test of the counting circuit — PHASE2_SPEC.md §A.3 as amended before Stage 19
# (Stage 19b B5); CLAUDE.md rule 9. The restoration in the circuit's own factors is proved in
# Lean (CQRV/Circuit/CountingCorrect.lean); this is the independent numerical check of the
# circuits and of the convention of §A.3 (5).
#
# Runs tests/diff/counting_diff.py: the circuits come from `lake env lean --run
# scripts/CertifyTool.lean counting-sample --all 4 tests/diff/counting/*.cqr` (one Lean start);
# for six predicates (n = 4 and 6; M = 0, 1, 5, 8, 9, 16) and m = 1..4: the phase-register
# distribution of the coherent circuit equals ½(P_m(θ/π) + P_m(−θ/π)) read with data n the MSB,
# the sampled MBU branches equal the coherent state, the negative controls (phase fix removed:
# the shifted mixture; bit-reversed reading: fails), the measured grades against the composed
# bound of Stage 19a, the block table replays to the circuit, and the AQFT variants at m = 4;
# parts (f), (g) (Stage 20a) and (h) (Stage 20b2: one predicate at m = 5, 6 in coherent mode and
# the AQFT variant at m = 6, four single-circuit `counting-sample` calls, about 70 s).
#
# Usage (after `lake build`):  scripts/diff_counting.sh [--m-max 4] [--seed S] [--samples 2]
#   PYTHON=.venv/Scripts/python.exe scripts/diff_counting.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
cd "$ROOT"
"$PY" -I "$ROOT/tests/diff/counting_diff.py" "$@"
