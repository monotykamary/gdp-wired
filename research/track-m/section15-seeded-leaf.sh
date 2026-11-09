#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
LAB_DISPOSABLE=1 bun research/track-m/section15-derive-variant.ts "$2"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section14.ts
out=$(mktemp -d "$HOME/track-m-seeded-leaf-$1-$2-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$out"' EXIT
timeout -s KILL 20 bun research/track-m/section15-seeded-leaf.ts fixtures/packet.json fixtures/seeds.json "fixtures/leaf$1.json" "$out"
