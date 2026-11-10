#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
work=$(mktemp -d /tmp/census-integrity-XXXXXX)
out="$work/results"
mkdir -p "$out"
trap 'status=$?; shopt -s nullglob; files=("$out"/*); if ((${#files[@]})); then bun "$root/research/track-m/pack-section7-receipts.ts" "${files[@]}"; fi; rm -rf "$work"; exit "$status"' EXIT
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check
(cd integrity-input && sha256sum -c archives.sha256)
for name in census tf1; do
 mkdir -p "$work/$name"
 tar xzf "integrity-input/$name.tar.gz" -C "$work/$name"
 rm -rf "$work/$name/node_modules" "$work/$name/vendor"
 ln -s "$root/node_modules" "$work/$name/node_modules"
 ln -s "$root/vendor" "$work/$name/vendor"
done
bun research/track-m/prepare-census-integrity.ts "$work" "$root" "$out"
bun research/track-m/run-census-integrity.ts "$work" "$root/replay-input/input.json" "$out"
