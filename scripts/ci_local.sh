#!/usr/bin/env bash
# Local CI — report §9.5.1, Table 9.5; Stage 9b ("CI stays local"; DECISIONS.md 2026-10-25).
#
# Runs, in order, every step of the `pinned` job of .github/workflows/ci.yml that can run on this
# machine and prints one line per step: PASS / FAIL (with the log file), or n/a for a step that
# has no local counterpart (checkout: the working tree is the checkout; elan install and
# setup-python: the local toolchain and the .venv are used; apt install of llvm: only when
# llvm-as is on PATH, otherwise the QIR check runs with llvmlite only). M2 acceptance is judged on
# this output. Keep the step list in sync with ci.yml.
# Pass mark since Stage 24b (the step "Hardware lowering"): 21 PASS, 0 FAIL, 4 n/a (20 PASS since
# Stage 24a, 19 since 21a4, 18 since 19b, 17 since 18b, 16 before). The two hardware steps run with
# .venv-hw (hw/README.md) and are n/a when that venv is absent.
#
# Usage (from anywhere):  scripts/ci_local.sh
#   PYTHON=<python> scripts/ci_local.sh   # default: .venv/Scripts/python.exe or .venv/bin/python
# Logs: .lake/ci_local/<k>-<step>.log (git-ignored). Exit 0 iff no step failed.
# Portable: bash; Git Bash on Windows and ubuntu.

set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"
LOGS="$ROOT/.lake/ci_local"
mkdir -p "$LOGS"
rm -f "$LOGS"/*.log

if [ -z "${PYTHON:-}" ]; then
  if [ -x .venv/Scripts/python.exe ]; then PYTHON="$ROOT/.venv/Scripts/python.exe"
  elif [ -x .venv/bin/python ]; then PYTHON="$ROOT/.venv/bin/python"
  else PYTHON=python; fi
fi
export PYTHON
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

k=0 pass=0 fail=0 na=0
step() {  # step <name> <command…>
  local name="$1"; shift
  k=$((k + 1))
  local log
  log="$LOGS/$(printf '%02d' "$k")-$(tr -c 'A-Za-z0-9' '_' <<<"$name" | cut -c1-40).log"
  local t0=$SECONDS
  if "$@" >"$log" 2>&1; then
    pass=$((pass + 1)); printf 'PASS  %2d  %s (%ds)\n' "$k" "$name" $((SECONDS - t0))
  else
    fail=$((fail + 1)); printf 'FAIL  %2d  %s (%ds; log: %s)\n' "$k" "$name" $((SECONDS - t0)) "$log"
  fi
}
skip() {  # skip <name> <reason>
  k=$((k + 1)); na=$((na + 1)); printf 'n/a   %2d  %s (%s)\n' "$k" "$1" "$2"
}

build() { set -o pipefail; lake build 2>&1 | tee "$LOGS/build.log"; }
sorries() { scripts/check_sorries.sh && scripts/check_sorries.sh --self-test; }
pyreqs() { "$PYTHON" -m pip install --no-deps -r tests/diff/requirements.lock && "$PYTHON" -m pip check; }
llvm() { llvm-as --version; }

echo "ci_local: $(git rev-parse --short HEAD)$(git diff --quiet && git diff --cached --quiet || echo ' + working tree'), python $("$PYTHON" --version 2>&1), LEAN_NUM_THREADS=$LEAN_NUM_THREADS"
skip "actions/checkout" "local working tree"
skip "Install elan" "local toolchain: $(lake --version 2>/dev/null | head -1)"
step "Fetch Mathlib cache" lake exe cache get
step "lake build" build
step "Warning check" scripts/check_warnings.sh "$LOGS/build.log"
step "Sorry check (+ self-test)" sorries
step "CLI smoke" scripts/cli_smoke.sh
step "Axiom audit (blocking)" scripts/print_axioms.sh
skip "actions/setup-python" "local venv: $PYTHON"
step "Install Python harness requirements (lock) + pip check" pyreqs
step "Simulator self-test" "$PYTHON" -I tests/diff/statevector.py --selftest
step "Differential oracle test" scripts/diff_oracles.sh
step "Front-end validation (Stage 9b)" scripts/diff_frontend.sh
step "Synthesized circuits = golden file" scripts/check_oracle_json.sh
step "Diffusion and Grover circuit" scripts/diff_grover.sh
step "Few-ancilla MCZ (Stage 12b; few:log certified, 12d; every n, 13a)" scripts/diff_mcz.sh
step "QFT / AQFT (Stage 18b)" scripts/diff_qft.sh
step "Counting circuit (Stage 19b)" scripts/diff_counting.sh
step "Second worked predicate simple_alu_x0_1 (Stage 9b)" scripts/diff_benchmark.sh
if command -v llvm-as >/dev/null 2>&1; then
  step "Install llvm (llvm-as present)" llvm
  step "SHA3, schema, QIR / QASM re-parse (REQUIRE_LLVM_AS=1)" env REQUIRE_LLVM_AS=1 scripts/check_emit.sh
else
  skip "Install llvm (apt)" "no apt / llvm-as on this machine"
  step "SHA3, schema, QIR / QASM re-parse (llvmlite; llvm-as absent)" scripts/check_emit.sh
fi
step "cqr certify (both predicates, few:log, negative tests)" scripts/check_certify.sh
step "Certified selection (Stage 21a4)" scripts/check_select.sh
if [ -x .venv-hw/Scripts/python.exe ] || [ -x .venv-hw/bin/python ]; then
  step "Hardware target (Stage 24a)" scripts/check_hw_target.sh
  step "Hardware lowering (Stage 24b)" scripts/check_hw_lower.sh
else
  skip "Hardware target (Stage 24a)" "no .venv-hw (hw/README.md)"
  skip "Hardware lowering (Stage 24b)" "no .venv-hw (hw/README.md)"
fi

echo "ci_local: $pass PASS, $fail FAIL, $na n/a (logs: .lake/ci_local/)"
[ "$fail" -eq 0 ]
