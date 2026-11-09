#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
out=$(mktemp -d "$HOME/track-m-lane-b-prepare-XXXXXX")
mkdir -p "$out/raw/before" "$out/raw/after" "$out/prepared"
trap 'bash research/track-m/pack-section18-archive.sh "$out/prepared"' EXIT
tar -xzf before/receipts.tar.gz -C "$out/raw/before"
tar -xzf after/receipts.tar.gz -C "$out/raw/after"
bun research/track-m/lane-b-family.ts "$out/prepared/family.json"
bun research/track-m/lane-b-prepare-replays.ts "$out/raw" "$out/prepared"
