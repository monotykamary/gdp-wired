#!/usr/bin/env bash
set -euo pipefail
tag=${1:?}; first=${2:?}; variant=${3:-native}
[[ "$first" == before || "$first" == after ]]
[[ "$variant" == native || "$variant" == flags ]]
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/completion-scope-$tag-$variant-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
cp core/counts.ts "$work/candidate-counts.source"
cp scope-input/before-counts.source "$work/control-counts.source"
cp scope-input/family.json "$work/family.json"
mkdir -p replays
cp scope-input/family.json replays/family.json
for side in "$first" "$([[ "$first" == before ]] && echo after || echo before)"; do
 if [[ "$side" == before ]]; then cp "$work/control-counts.source" core/counts.ts; else cp "$work/candidate-counts.source" core/counts.ts; fi
 if [[ "$variant" == flags ]]; then LAB_DISPOSABLE=1 bun research/track-m/member-premises-variant.ts flags; fi
 cp core/counts.ts "$work/$side-counts.ts"
 echo "COMPLETION_PAIR_BEGIN $tag $variant $side"
 LANE_B_PASS_ORDER=count-first LANE_B_OUT="$work/$side" bash research/track-m/lane-b-section16.sh "$tag" > "$work/$side.log" 2>&1
 bun research/track-m/audit-lane-b-cost.ts "$work/$side/$tag/capture.json.gz" replays/family.json
 echo "COMPLETION_PAIR_END $tag $variant $side"
done
