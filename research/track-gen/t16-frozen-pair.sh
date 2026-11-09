#!/usr/bin/env bash
# Immutable-commit iteration probe; NOT Lane D's authoritative final gate.
set -euo pipefail
root=$PWD
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
mkdir -p "$scratch/candidate"
tar -xf "$root/frozen/candidate.tar" -C "$scratch/candidate"
mkdir -p "$scratch/candidate/vendor"
cp -R "$root/vendor/." "$scratch/candidate/vendor/"
ln -s "$root/frozen" "$scratch/candidate/baselines"
printf 'ITERATION_REVISIONS candidate=c9d7f823 baseline=b788e195\n'
sha256sum "$root/frozen/candidate.tar" "$root/frozen/main.tar"
cd "$scratch/candidate"
bash research/track-gen/t14-paired.sh original "$1" "$2" main
