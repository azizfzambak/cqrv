#!/usr/bin/env bash
# Candidate-toolchain build — report Table 9.5 (dependency-drift row: "CI green on both
# pinned and candidate toolchains"), §9.5.3.
#
# Copies the working tree (without .git and .lake) to a temporary directory, points the copy
# at the newest Mathlib *release* tag and that tag's own lean-toolchain, and runs the same
# build and checks as the pinned job. The committed pins (lean-toolchain, lakefile.lean,
# lake-manifest.json) are never modified (CLAUDE.md rule 4).
#
# Usage: scripts/candidate_build.sh [workdir]     (default: ${RUNNER_TEMP:-/tmp}/cqrv-candidate)
# Portable: bash, git, curl, POSIX sed/sort/grep (no sed -i, no sort -V); ubuntu and Git Bash.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK="${1:-${RUNNER_TEMP:-/tmp}/cqrv-candidate}"
MATHLIB=https://github.com/leanprover-community/mathlib4

# Newest release tag vX.Y.Z (no -rc), compared numerically field by field.
TAG="$(git ls-remote --tags --refs "$MATHLIB.git" 'v4.*' | sed 's#.*refs/tags/##' \
        | grep -E '^v[0-9]+\.[0-9]+\.[0-9]+$' \
        | sed 's/^v//' | sort -t. -k1,1n -k2,2n -k3,3n | tail -n 1 | sed 's/^/v/')"
[ -n "$TAG" ] || { echo "candidate: could not determine newest Mathlib release tag" >&2; exit 1; }
TOOLCHAIN="$(curl -fsSL "https://raw.githubusercontent.com/leanprover-community/mathlib4/$TAG/lean-toolchain")"
echo "candidate: Mathlib $TAG, toolchain $TOOLCHAIN (pinned: $(cat "$ROOT/lean-toolchain"))"

rm -rf "$WORK"; mkdir -p "$WORK"
(cd "$ROOT" && tar --exclude=./.git --exclude=./.lake --exclude=./.venv -cf - .) | (cd "$WORK" && tar -xf -)
cd "$WORK"
printf '%s\n' "$TOOLCHAIN" > lean-toolchain
sed -E "s#(mathlib4\.git\" @ \")[^\"]+\"#\1$TAG\"#" lakefile.lean > lakefile.lean.new
mv lakefile.lean.new lakefile.lean
grep -q "@ \"$TAG\"" lakefile.lean || { echo "candidate: failed to retarget lakefile" >&2; exit 1; }

lake update mathlib
lake exe cache get
lake build 2>&1 | tee build.log
scripts/check_warnings.sh build.log
scripts/check_sorries.sh
scripts/print_axioms.sh
