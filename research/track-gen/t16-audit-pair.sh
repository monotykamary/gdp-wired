#!/usr/bin/env bash
# Immutable iteration measurements. Not Lane D's authoritative final gate.
set -euo pipefail
root=$PWD
mode=${1:?mode}
id=${2:?protocol}
repeat=${3:?repeat}
test "$(git get-tar-commit-id < "$root/frozen/candidate.tar")" = "$CANDIDATE_COMMIT"
test "$(git get-tar-commit-id < "$root/frozen/main.tar")" = "$BASELINE_COMMIT"
printf 'ITERATION_REVISIONS candidate=%s baseline=%s\n' "$CANDIDATE_COMMIT" "$BASELINE_COMMIT"
sha256sum "$root/frozen/candidate.tar" "$root/frozen/main.tar"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
mkdir -p "$scratch/candidate"
tar -xf "$root/frozen/candidate.tar" -C "$scratch/candidate"
mkdir -p "$scratch/candidate/vendor"
cp -R "$root/vendor/." "$scratch/candidate/vendor/"
# Execution-only repair: the archived driver predates side-exit propagation.
# Keep the measured engine immutable, but use the fixed paired launcher.
cp "$root/research/track-gen/t14-paired.sh" "$scratch/candidate/research/track-gen/t14-paired.sh"
ln -s "$root/frozen" "$scratch/candidate/baselines"
cd "$scratch/candidate"
bash research/track-gen/t14-paired.sh "$mode" "$id" "$repeat" main
