#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
work=$(mktemp -d /tmp/section11-diagnostic-XXXXXX)
out="$work/results"
mkdir -p "$out" "$work/full"
trap 'status=$?; shopt -s nullglob; files=("$out"/*); if ((${#files[@]})); then bun "$root/research/track-m/pack-section10-archive.ts" "${files[@]}"; fi; rm -rf "$work"; exit "$status"' EXIT
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check > "$out/check.log" 2>&1
cp -a core kernel research package.json tsconfig.json "$work/full/"
ln -s "$root/node_modules" "$work/full/node_modules"
ln -s "$root/vendor" "$work/full/vendor"
(cd "$work/full"; TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section10-diagnostic.ts family > "$out/install.json"; DIAG_OUTPUT="$out" TRACK_M_FAMILY_TRACE=1 timeout -s KILL 360 bun research/track-m/run-section11-family-diagnostic.ts "$root/replay-input/input.json" > "$out/full.log" 2>&1)
