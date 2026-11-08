#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
out=$(mktemp -d /tmp/section10-ta-XXXXXX)
trap 'status=$?; shopt -s nullglob; files=("$out"/*.json "$out"/*.jsonl "$out"/*.stderr.log); if ((${#files[@]})); then bun "$root/research/track-m/pack-section10-receipts.ts" "${files[@]}"; fi; rm -rf "$out"; exit "$status"' EXIT
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check
bun test research/track-m/section9-ta-audit.test.ts research/track-m/section10-ta-audit.test.ts core/count-recovery/conditional-proof.test.ts core/count-recovery/conditional-check-cache.test.ts
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section10-ta.ts
bun research/track-m/run-section10-ta.ts "$out"
if [[ -z "${LAB_SECTION10_DEBUG:-}" ]]; then
 for id in A1 B1 A2 B2 A3 B3; do
  timeout -s KILL 60 bun research/track-m/verify-section10-ta.ts "$out/$id.json" >> "$out/validation.jsonl"
 done
fi
