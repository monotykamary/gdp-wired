#!/usr/bin/env bash
set -euo pipefail
law=$1; op=$2; variant=$3
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
LAB_DISPOSABLE=1 bun research/track-m/lane-b-variant.ts "$variant"
LAB_DISPOSABLE=1 bun research/track-m/install-lane-b-op.ts
out=$(mktemp -d "$HOME/track-m-lane-b-op-$law-$op-$variant-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$out"' EXIT
timeout -s KILL 15 bun research/track-m/lane-b-op.ts "packets/$law.packet.json" "$op" "$out"
