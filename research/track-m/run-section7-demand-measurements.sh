#!/usr/bin/env bash
# Measurements only: the production pool, proof search and budgets are unchanged.
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check
export LAB_DEMAND_PROPOSALS=1 LAB_SOURCE_MS=5000 LAB_SOURCE_TRACE=1 LAB_CONDITIONAL_PROOF=1
export LAB_SECTION7_CAPTURE=v7-input/demand-and-sources.log
for law in 'Inv*' Inv2973; do
 for target in 0 1; do
  LAB_SECTION7_MEASUREMENT=T2 LAB_SECTION7_TARGET="$target" timeout -s KILL 90 bun research/track-m/active-source-probe.ts replay-input/input.json "$law" 5 all
 done
 LAB_SECTION7_MEASUREMENT=T3 timeout -s KILL 30 bun research/track-m/active-source-probe.ts replay-input/input.json "$law" 5 all
done
