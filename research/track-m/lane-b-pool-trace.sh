#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/track-m-pool-observation-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
mkdir "$work/original"
tar -xzf archive/receipts.tar.gz -C "$work/original"
bun run check
bun scripts/test-shards.ts --list > "$work/merged-shards.txt"
bun test core/runtime-default.test.ts core/compare.test.ts core/mutate.test.ts core/extract-absence.test.ts core/extract-choice-joins.test.ts core/count-ranges.test.ts core/counts-completion-order.test.ts
echo MERGED_SOURCE_CHECK_OK
cp "$work/original/after-counts.ts" core/counts.ts
sha256sum -c "$work/original/after.sha256"
cp "$work/original/family.json" "$work/family.json"
mkdir -p replays
cp "$work/family.json" replays/family.json
cp core/counts.ts "$work/uninstrumented-counts.ts"
LAB_DISPOSABLE=1 bun research/track-m/observe-lane-b-pool-variant.ts
cp core/counts.ts "$work/observed-counts.ts"
bunx commitlint --default-config < archive/commit-message.txt
LANE_B_PASS_ORDER=count-first LANE_B_OUT="$work/trace" bash research/track-m/lane-b-section16.sh star > "$work/trace.log" 2>&1
bun research/track-m/project-lane-b-pool-trace.ts "$work/trace/star/capture.json.gz" | tee "$work/runtime-pool.json"
