#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
out=$(mktemp -d /tmp/section9-ta-XXXXXX)
trap 'status=$?; shopt -s nullglob; files=("$out"/*.json "$out"/*.stderr.log); if ((status)); then files+=("$out"/*.capture.log); fi; if ((${#files[@]})); then bun "$root/research/track-m/pack-section7-receipts.ts" "${files[@]}"; fi; rm -rf "$out"; exit "$status"' EXIT
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section9-ta.ts
bun research/track-m/run-section9-ta.ts "$out"
