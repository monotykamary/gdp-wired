#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d /tmp/section8-loop-XXXXXX)
trap 'status=$?; shopt -s nullglob; files=("$work"/*.log); if ((${#files[@]})); then bun research/track-m/pack-section7-receipts.ts "${files[@]}"; fi; rm -rf "$work"; exit "$status"' EXIT
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section8-loop.ts
export LAB_DEMAND_PROPOSALS=1 LAB_SOURCE_MS=5000 LAB_SOURCE_TRACE=1 LAB_CONDITIONAL_PROOF=1
if [[ "${LAB_SECTION8_FULL_POOL:-0}" == 1 ]]; then
 unset LAB_SECTION7_MEASUREMENT LAB_SECTION7_CLEAN_WITNESSES
else
 export LAB_SECTION7_CAPTURE=v7-input/demand-and-sources.log LAB_SECTION7_MEASUREMENT=T2 LAB_SECTION7_CLEAN_WITNESSES=1
fi
for law in 'Inv*' Inv2973; do
 if [[ "$law" == 'Inv*' ]]; then file=loop-star.log; else file=loop-overlap.log; fi
 timeout -s KILL 90 bun research/track-m/active-source-probe.ts replay-input/input.json "$law" 5 all > "$work/$file"
done
timeout -s KILL 180 bun run check
