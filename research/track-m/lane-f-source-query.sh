#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/lane-f-source-query-XXXXXX")
trap 'status=$?; if [[ $status -ne 0 && -f "$work/result.log" ]]; then tail -n 10 "$work/result.log"; fi; bash research/track-m/pack-section18-archive.sh "$work"; exit "$status"' EXIT
if [[ "$1" == *selectors* ]]; then LAB_DISPOSABLE=1 bun research/track-m/lane-f-selector-variant.ts; fi
timeout 15s bun research/track-m/lane-f-source-query.ts context.json trace.json "$1" "$work/output" > "$work/result.log" 2>&1
tail -n 1 "$work/result.log"
