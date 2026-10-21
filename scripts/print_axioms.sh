#!/usr/bin/env bash
# Axiom audit — report §9.5.1 (master discipline), CLAUDE.md rule 10.
#
# Prints `#print axioms`-equivalent output for every theorem declared in a module under
# CQRV/Certify (via scripts/PrintAxioms.lean, run with `lake env lean` after `lake build`).
# Prints "no theorems in CQRV.Certify" when there are none.
#
# Stage 0–7: informational only — this script always exits 0 if Lean runs.
# Stage 8: becomes blocking — it must fail on `sorryAx` or on any axiom outside the listed
# trust boundary (propext, Classical.choice, Quot.sound, plus entries in docs/DECISIONS.md).
#
# Portable: bash only; ubuntu and Git Bash on Windows.

set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/PrintAxioms.lean 2>&1 | tr -d '\r' | sed -E 's/^.*PrintAxioms\.lean:[0-9]+:[0-9]+: (info: )?//'
