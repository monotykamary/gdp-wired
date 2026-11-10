#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check
bun test core/quorum-laws.test.ts core/small-counts.test.ts core/wall.test.ts
out=$(mktemp -d "$HOME/track-m-lane-b-baseline-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$out"' EXIT
bun research/track-m/lane-b-family.ts "$out/family.json"
target=${1:?one target per VM required}
timeout -s KILL 20 bun research/track-m/lane-b-cost.ts "$out/family.json" "$target" "$out/$target" 2700
