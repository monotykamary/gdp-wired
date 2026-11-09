#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/lane-f-original-family-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
LAB_DISPOSABLE=1 GDP_COUNTS_TRACE=3 timeout 65s bun research/track-m/lane-f-capture-original.ts "$work/family.json"
timeout 20s bun research/track-m/lane-b-cost.ts "$work/family.json" overlap "$work/baseline" 6000 7000
