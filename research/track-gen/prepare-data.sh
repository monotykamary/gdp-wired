#!/usr/bin/env bash
# Only operate in this checkout. No other worktree is required.
set -euo pipefail
out=${1:-runs/track-gen-data}
mkdir -p "$out"
cp research/track-gen/input.json "$out/input.json"
git archive 3394e14c > "$out/parent.tar"
git archive 6a3874d3 > "$out/main.tar"
shasum -a 256 "$out/input.json" "$out/parent.tar" "$out/main.tar"
