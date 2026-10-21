#!/usr/bin/env bash
# Warning check — CLAUDE.md rule 3, report §9.5.1.
#
# Fails if a `lake build` log contains a warning located in one of our own source files
# (CQRV.lean, CQRV/, Apps/, tests/) other than "declaration uses 'sorry'" (those are policed
# separately by scripts/check_sorries.sh against docs/SORRIES.md). Lean ≥ 4.2x quotes it with
# backticks (declaration uses `sorry`); both quotings are accepted.
#
# Scope (reviewer decision, docs/DECISIONS.md 2026-10-21): warnings from dependencies
# (Mathlib, Physlib, … under .lake/ or with their own relative paths) and warnings that name
# no source file are ignored. Lake replays the stored log of up-to-date modules, so warnings
# in our files stay visible on rebuilds.
#
# Usage:  lake build 2>&1 | tee build.log; scripts/check_warnings.sh build.log
# Portable: bash + POSIX awk (mawk/gawk); ubuntu and Git Bash on Windows.

set -euo pipefail

log="${1:?usage: $0 <lake build log>}"
[ -f "$log" ] || { echo "check_warnings: no such log: $log" >&2; exit 2; }

# Windows paths: normalize backslashes to "/" before matching.
bad="$(tr -d '\r' < "$log" | tr '\\' '/' | awk '
  tolower($0) !~ /(^|[^[:alnum:]_])warning:/ { next }
  /declaration uses .sorry./ { next }
  {
    # Source position "path.lean:line:col" (lake: "warning: p:l:c: msg"; lean: "p:l:c: warning: msg").
    if (!match($0, /[^[:space:]:]+\.lean:[0-9]+:[0-9]+/)) next
    path = substr($0, RSTART, RLENGTH); sub(/\.lean:.*/, ".lean", path)
    while (sub(/^\.\//, "", path)) {}
    if (path ~ /(^|\/)\.lake\//) next                                  # dependency
    if (path == "CQRV.lean" || path ~ /^(CQRV|Apps|tests)\//) print    # relative, ours
    else if (path ~ /^(\/|[A-Za-z]:)/ && path ~ /\/(CQRV\.lean|(CQRV|Apps|tests)\/)/) print  # absolute
  }')"

if [ -n "$bad" ]; then
  echo "check_warnings: FAIL — warnings in CQRV/, Apps/ or tests/ other than \"declaration uses 'sorry'\":"
  printf '%s\n' "$bad"
  exit 1
fi
echo "check_warnings: OK (no warnings in our sources besides tracked sorries)"
