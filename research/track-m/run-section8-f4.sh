#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d /tmp/section8-f4-XXXXXX)
trap 'status=$?; bun research/track-m/pack-section7-receipts.ts "$work"/*.log; rm -rf "$work"; exit "$status"' EXIT
bun research/track-m/install-section8-progress.ts
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-phase-census.ts "$work/original"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section7-cost.ts --followup
cp kernel/prover-rows.ts "$work/prover-rows.ts"
cp research/track-m/section8-incremental-rows.ts "$work/incremental-rows.ts"
cp research/track-m/run-phase-census.ts "$work/runner.ts"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section8-f4.ts
bun test research/track-m/section8-incremental-rows.test.ts
cp "$work/prover-rows.ts" kernel/prover-rows.ts
cp "$work/incremental-rows.ts" research/track-m/section8-incremental-rows.ts
cp "$work/runner.ts" research/track-m/run-phase-census.ts
LAB_SECTION7_T1=1 TRACK_M_PHASE_CENSUS=1 timeout -s KILL 300 bun research/track-m/run-phase-census.ts focused replay-input/input.json tf4-control > "$work/tf4-control.log"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section8-f4.ts
bun test research/track-m/section8-incremental-rows.test.ts
LAB_SECTION7_T1=1 TRACK_M_PHASE_CENSUS=1 timeout -s KILL 300 bun research/track-m/run-phase-census.ts focused replay-input/input.json tf4-incremental > "$work/tf4-incremental.log"
timeout -s KILL 180 bun run check
