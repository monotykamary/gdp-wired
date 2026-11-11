#!/usr/bin/env bash
set -euo pipefail
repo=$(git rev-parse --show-toplevel)
input=${1:?output directory}; pin=${2:?candidate source pin}
mkdir -p "$input"; input=$(cd "$input" && pwd)
git -C "$repo" rev-parse "$pin" > "$input/source.txt"
git -C "$repo" archive "$pin" > "$input/source.tar"
git -C "$repo" archive 5aa7681815e41a939fed137783b656abeeacc1e6 > "$input/baseline.tar"
git -C "$repo" ls-tree -r becd98e30bf4b7df29217fa820b82b7aa259bf28 kernel lean-kernel > "$input/trusted-tree.txt"
for module in gdp-ts handwired; do
 hash=$(git -C "$repo" rev-parse "$pin:vendor/$module")
 git -C "$repo/vendor/$module" archive --prefix="vendor/$module/" "$hash" > "$input/$module.tar"
done
cp "$repo"/research/lane-i/candidate/*.ts "$input/"
cp "$repo/research/lane-i/candidate/pins.json" "$input/"
(cd "$input"; sha256sum source.tar gdp-ts.tar handwired.tar > SHA256SUMS)
