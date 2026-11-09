#!/usr/bin/env bash
set -euo pipefail
tag=${1:?target}; first=${2:?before or after}
[[ "$first" == before || "$first" == after ]]
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/track-m-demand-$tag-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
mkdir -p "$work/control" "$work/candidate/core"
tar xf replays/control.tar -C "$work/control"
cp core/counts.ts core/count-ranges.ts "$work/candidate/core/"
cp replays/family.json "$work/family.json"
sha256sum replays/family.json > "$work/family.sha256"
for side in "$first" "$([[ "$first" == before ]] && echo after || echo before)"; do
 if [[ "$side" == before ]]; then source="$work/control"; else source="$work/candidate"; fi
 cp "$source/core/counts.ts" "$source/core/count-ranges.ts" core/
 sha256sum core/counts.ts core/count-ranges.ts > "$work/$side.sha256"
 mkdir -p "$work/$side-source/core"
 cp core/counts.ts core/count-ranges.ts "$work/$side-source/core/"
 echo "DEMAND_BEGIN $tag $side"
 LANE_B_PASS_ORDER=count-first LANE_B_OUT="$work/$side" bash research/track-m/lane-b-section16.sh "$tag" > "$work/$side.log" 2>&1
 bun -e 'const r=await Bun.file(process.argv[1]).json();const {events,profile,...brief}=r;console.log(JSON.stringify({side:process.argv[2],...brief}))' "$work/$side/$tag/summary.json" "$side"
 echo "INPUT=$tag-$side.json.gz" | tee -a "$work/audit.log"
 bun research/track-m/audit-lane-b-cost.ts "$work/$side/$tag/capture.json.gz" replays/family.json | tee -a "$work/audit.log"
 echo "DEMAND_END $tag $side"
done
