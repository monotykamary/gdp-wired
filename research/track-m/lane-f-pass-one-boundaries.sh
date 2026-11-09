#!/usr/bin/env bash
set -euo pipefail
[[ $# -eq 1 && "$1" =~ ^[0-6]$ ]]
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/lane-f-pass-one-boundaries-XXXXXX")
trap 'status=$?; bash research/track-m/pack-section18-archive.sh "$work"; exit "$status"' EXIT
LAB_DISPOSABLE=1 bun research/track-m/lane-f-step-only-variant.ts
LAB_DISPOSABLE=1 bun research/track-m/lane-f-phase-boundaries-variant.ts
sha256sum family.json core/counts.ts core/finite-model.ts
GDP_COUNTS_DUMP_ALL_PASSES=1 timeout 15s bun research/track-m/lane-f-pass-one-boundaries.ts family.json overlap "$1" "$work/result"
