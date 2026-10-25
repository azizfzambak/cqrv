#!/usr/bin/env bash
# Kernel-check benchmark — report §9.5.1 (reference configuration; the report's 0.3 s is a
# target for a 3 GHz core), Stage 8b reviewer decision 6 (DECISIONS.md 2026-10-25).
#
# Prints the machine (CPU model, logical CPUs, clock if available), the Lean version and the
# Mathlib / Physlib revisions, then for both committed certificates (Stage 9b) runs
#   cqr certify examples/grover_pred_037.cqr --out examples/certs/grover_pred_037 --bench N --report
#   cqr certify examples/simple_alu_x0_1.cqr --solutions M --out examples/certs/simple_alu_x0_1 #     --bench N --report
# (M of the second predicate is counted by the Python harness, tests/diff/benchmark_diff.py, as a
# test oracle only; the certificate stays conditional on solution_count = M), each of which
# kernel-checks the certificate N + 1 times (`lake env lean -Dprofiler=true Cert.lean`)
# and records the median of the last N (the first run is excluded: cold file cache) in the
# certificate's reference_configuration.kernel_check: wall_ms (process start, imports,
# elaboration, kernel) and kernel_ms (the profiler's `type checking`), and writes the run report
# (run_report.md / run_report.json, Table 8.5.2). The measured value is recorded as is; nothing is
# tuned for the target.
#
# Usage (after `lake build`, from anywhere):  scripts/bench_kernel.sh [N]   (default N = 5)
#   PYTHON=.venv/Scripts/python.exe scripts/bench_kernel.sh   # local Windows venv
# Portable: bash + grep + sed; ubuntu and Git Bash on Windows.

set -euo pipefail
cd "$(dirname "$0")/.."
N="${1:-5}"
PY="${PYTHON:-python}"

rev() {  # rev <package name>: the "rev" of that package in lake-manifest.json
  tr -d '\r\n' < lake-manifest.json | grep -oE "\"rev\": \"[0-9a-f]{40}\",[^}]*\"name\": \"$1\"" \
    | sed -E 's/^"rev": "([0-9a-f]{40})".*/\1/'
}

echo "== machine"
if [ "${OS:-}" != "Windows_NT" ] && [ -r /proc/cpuinfo ]; then
  echo "cpu:          $(grep -m1 'model name' /proc/cpuinfo | sed -E 's/^[^:]*: *//')"
  echo "logical cpus: $(grep -c '^processor' /proc/cpuinfo)"
  f=/sys/devices/system/cpu/cpu0/cpufreq/cpuinfo_max_freq
  if [ -r "$f" ]; then echo "clock:        $(( $(cat "$f") / 1000 )) MHz (max)"; else echo "clock:        n/a"; fi
elif command -v powershell >/dev/null 2>&1; then
  powershell -NoProfile -NonInteractive -Command \
    '$p = Get-CimInstance Win32_Processor | Select-Object -First 1; "cpu:          $($p.Name)"; "logical cpus: $($p.NumberOfLogicalProcessors)"; "clock:        $($p.MaxClockSpeed) MHz (max)"' \
    | tr -d '\r'
else
  echo "cpu:          $(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo n/a)"
  echo "logical cpus: $(sysctl -n hw.logicalcpu 2>/dev/null || echo n/a)"
fi
echo "LEAN_NUM_THREADS: ${LEAN_NUM_THREADS:-unset}"
echo "== toolchain"
echo "lean:    $(lake env lean --version | tr -d '\r')"
echo "pinned:  $(tr -d '\r' < lean-toolchain)"
echo "mathlib: $(rev mathlib)"
echo "physlib: $(rev Physlib)"
M_ALU="$("$PY" -I -c 'import sys; sys.path.insert(0, "tests/diff"); import benchmark_diff as b; print(sum(1 for x in range(64) if b.reference(b.input_bits(x))))' | tr -d '\r')"
echo "M(simple_alu_x0_1) = $M_ALU (enumerated by tests/diff/benchmark_diff.py; test oracle only)"
for spec in "grover_pred_037:" "simple_alu_x0_1:--solutions $M_ALU"; do
  name="${spec%%:*}"
  extra="${spec#*:}"
  echo "== $name: kernel check (1 + $N runs, first excluded)"
  # shellcheck disable=SC2086
  lake exe cqr certify "examples/$name.cqr" $extra --out "examples/certs/$name" \
    --bench "$N" --report | tr -d '\r'
  echo "== $name: reference_configuration (examples/certs/$name/certificate.json)"
  grep -oE '"reference_configuration":\{[^{}]*(\{[^{}]*\}[^{}]*)?\}' \
    "examples/certs/$name/certificate.json"
done
