#!/usr/bin/env bash
set -euo pipefail
repeat=${1:?repeat}
shift
root=$PWD
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
base="$scratch/base"
mkdir -p "$base"
tar -xf "baselines/${BASE_KIND:-generation}.tar" -C "$base"
mkdir -p "$base/vendor"
cp -R "$root/vendor/." "$base/vendor/"
bun install --frozen-lockfile >/dev/null
(cd "$base" && bun install --frozen-lockfile >/dev/null)
for side in baseline candidate; do
  dir=$base
  [[ $side == candidate ]] && dir=$root
  code=0
  echo "TEST_SIDE $side repeat=$repeat"
  (cd "$dir" && bun test "$@") || code=$?
  echo "TEST_EXIT $side $code"
done
