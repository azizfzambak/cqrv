#!/usr/bin/env bash
# Kernel-check benchmark — report §9.5.1 (reference configuration; the report's 0.3 s is a
# target for a 3 GHz core), Stage 8b reviewer decision 6 (DECISIONS.md 2026-10-25).
#
# Prints the machine (CPU model, logical CPUs, clock if available), the Lean version and the
# Mathlib / Physlib revisions, then runs
#   cqr certify examples/grover_pred_037.cqr --out examples/certs/grover_pred_037 --bench N
# which kernel-checks the certificate N + 1 times (`lake env lean -Dprofiler=true Cert.lean`)
# and records the median of the last N (the first run is excluded: cold file cache) in the
# certificate's reference_configuration.kernel_check: wall_ms (process start, imports,
# elaboration, kernel) and kernel_ms (the profiler's `type checking`). The measured value is
# recorded as is; nothing is tuned for the target.
#
# Usage (after `lake build`, from anywhere):  scripts/bench_kernel.sh [N]   (default N = 5)
# Portable: bash + grep + sed; ubuntu and Git Bash on Windows.

set -euo pipefail
cd "$(dirname "$0")/.."
N="${1:-5}"

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
echo "== kernel check (1 + $N runs, first excluded)"
lake exe cqr certify examples/grover_pred_037.cqr --out examples/certs/grover_pred_037 \
  --bench "$N" | tr -d '\r'
echo "== reference_configuration (examples/certs/grover_pred_037/certificate.json)"
grep -oE '"reference_configuration":\{[^{}]*(\{[^{}]*\}[^{}]*)?\}' \
  examples/certs/grover_pred_037/certificate.json
