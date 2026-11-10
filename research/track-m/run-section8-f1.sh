#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d /tmp/section8-f1-XXXXXX)
trap 'status=$?; bun research/track-m/pack-section7-receipts.ts "$work"/*.log; rm -rf "$work"; exit "$status"' EXIT
bun research/track-m/install-section8-progress.ts
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-phase-census.ts "$work/original"
TRACK_M_PHASE_CENSUS=1 timeout -s KILL 300 bun research/track-m/run-phase-census.ts focused replay-input/input.json tf1-control > "$work/tf1-control.log"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section8-f1.ts
TRACK_M_PHASE_CENSUS=1 timeout -s KILL 300 bun research/track-m/run-phase-census.ts focused replay-input/input.json tf1-deferred > "$work/tf1-deferred.log"
timeout -s KILL 180 bun run check
