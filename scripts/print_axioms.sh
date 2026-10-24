#!/usr/bin/env bash
# Axiom audit — report §9.5.1 (master discipline), §9.5.3, CLAUDE.md rule 10.
#
# Blocking since Stage 8b (DECISIONS.md 2026-10-25):
#   1. every named theorem declared in a module under CQRV/Certify (scripts/PrintAxioms.lean;
#      auto-generated injEq / sizeOf_spec / eq_* lemmas are skipped) must pass
#      CQRV.Certify.auditAxioms: no sorryAx, only propext, Classical.choice, Quot.sound or an
#      entry of the trust-boundary table (CQRV/Certify/Audit.lean, empty today);
#   2. the committed example certificate examples/certs/grover_pred_037/Cert.lean must
#      kernel-check and its theorem `cert` must pass the same audit
#      (scripts/CertifyTool.lean `audit`).
# Exits non-zero on any failure. Run after `lake build`.
#
# Portable: bash only; ubuntu and Git Bash on Windows.

set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/PrintAxioms.lean 2>&1 | tr -d '\r' \
  | sed -E 's/^.*PrintAxioms\.lean:[0-9]+:[0-9]+: (info: )?//'
lake env lean --run scripts/CertifyTool.lean audit \
  examples/certs/grover_pred_037/Cert.lean CQRV.Cert.grover_pred_037.cert
