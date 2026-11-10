#!/usr/bin/env bash
set -euo pipefail
tag=${1:?target}; first=${2:?before or after}
[[ "$first" == before || "$first" == after ]]
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/track-m-range-$tag-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
mkdir -p "$work/control"; tar xf replays/control.tar -C "$work/control"
cp core/counts.ts "$work/candidate-counts.ts"
cp replays/family.json "$work/family.json"
sha256sum replays/family.json > "$work/family.sha256"
for side in "$first" "$([[ "$first" == before ]] && echo after || echo before)"; do
 if [[ "$side" == before ]]; then cp "$work/control/core/counts.ts" core/counts.ts; else cp "$work/candidate-counts.ts" core/counts.ts; fi
 sha256sum core/counts.ts core/count-ranges.ts > "$work/$side.sha256"
 cp core/counts.ts "$work/$side-counts.ts"
 echo "RANGE_BEGIN $tag $side"
 LANE_B_PASS_ORDER=count-first LANE_B_OUT="$work/$side" bash research/track-m/lane-b-section16.sh "$tag" > "$work/$side.log" 2>&1
 bun -e 'const r=await Bun.file(process.argv[1]).json();const {events,profile,...brief}=r;console.log(JSON.stringify({side:process.argv[2],...brief}))' "$work/$side/$tag/summary.json" "$side"
 echo "RANGE_END $tag $side"
done
