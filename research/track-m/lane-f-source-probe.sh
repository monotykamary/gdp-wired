#!/usr/bin/env bash
set -euo pipefail
[[ $# -eq 1 ]]
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/lane-f-source-probe-XXXXXX")
trap 'status=$?; bash research/track-m/pack-section18-archive.sh "$work"; exit "$status"' EXIT
sha256sum context.json offdiag-trace.json family.json core/count-write-frames.ts research/track-m/lane-f-source-query.ts
LAB_SOURCE_UNITS=1000 bun research/track-m/lane-f-source-query.ts context.json offdiag-trace.json "$1" "$work/result"
