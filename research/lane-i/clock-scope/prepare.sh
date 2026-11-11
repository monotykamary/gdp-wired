#!/usr/bin/env bash
set -euo pipefail
repo=$(git rev-parse --show-toplevel)
input=${1:?usage: bash research/lane-i/clock-scope/prepare.sh OUTPUT-DIRECTORY}
mkdir -p "$input"
input=$(cd "$input" && pwd)
git -C "$repo" archive 5aa7681815e41a939fed137783b656abeeacc1e6 > "$input/source.tar"
git -C "$repo" ls-tree -r 5aa7681815e41a939fed137783b656abeeacc1e6 kernel lean-kernel > "$input/trusted-tree.txt"
for module in gdp-ts handwired; do
  hash=$(git -C "$repo" rev-parse "5aa76818:vendor/$module")
  git -C "$repo/vendor/$module" archive --prefix="vendor/$module/" "$hash" > "$input/$module.tar"
done
for file in clock-only.patch clock-tripwire.test.source clock-tripwire-preload.source verify.ts COMMIT.txt; do
  cp "$repo/research/lane-i/clock-scope/$file" "$input/$file"
done
sha256sum "$input/source.tar" "$input/clock-only.patch"
