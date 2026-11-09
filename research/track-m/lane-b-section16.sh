#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
if [[ -n "${LEAF_VARIANT:-}" ]]; then LAB_DISPOSABLE=1 bun research/track-m/section15-leaf-variant.ts "$LEAF_VARIANT"; fi
if [[ -n "${DERIVE_VARIANT:-}" ]]; then LAB_DISPOSABLE=1 bun research/track-m/section15-derive-variant.ts "$DERIVE_VARIANT"; fi
if [[ "${PROFILE_CHECKS:-0}" == 1 ]]; then LAB_DISPOSABLE=1 bun research/track-m/install-check-cost-profile.ts; fi
out=${LANE_B_OUT:-$(mktemp -d "$HOME/track-m-lane-b-section16-$1-XXXXXX")}
mkdir -p "$out"
trap 'bash research/track-m/pack-section18-archive.sh "$out"' EXIT
DUMP_DIR="$out/dump" DUMP_ALL=1 DUMP_MIN=0 DUMP_N=100000 timeout -s KILL 20 bun --preload ./research/query/dump.ts research/track-m/lane-b-cost.ts replays/family.json "$1" "$out/$1" 6000 7000
