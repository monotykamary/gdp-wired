#!/usr/bin/env bash
set -euo pipefail
tag=${1:?target}; first=${2:?before or after}
variant=${LANE_B_VARIANT:-member-premises}
[[ "$variant" == member-premises || "$variant" == row-premises || "$variant" == early-completion || "$variant" == flags-first || "$variant" == unary-completion ]]
[[ "$first" == before || "$first" == after ]]
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/track-m-members-$tag-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
if [[ "$variant" == unary-completion ]]; then
 LAB_DISPOSABLE=1 bun research/track-m/member-premises-variant.ts flags
fi
cp core/counts.ts "$work/before-counts.ts"
if [[ "$variant" == flags-first ]]; then
 LAB_DISPOSABLE=1 bun research/track-m/member-premises-variant.ts flags
else
 LAB_DISPOSABLE=1 bun "research/track-m/$variant-variant.ts"
fi
cp core/counts.ts "$work/after-counts.ts"
cp replays/family.json "$work/family.json"
sha256sum replays/family.json > "$work/family.sha256"
for side in "$first" "$([[ "$first" == before ]] && echo after || echo before)"; do
 cp "$work/$side-counts.ts" core/counts.ts
 sha256sum core/counts.ts core/count-ranges.ts core/count-recovery/member-premises.ts core/count-recovery/row-premises.ts > "$work/$side.sha256"
 echo "VARIANT_BEGIN $variant $tag $side"
 LANE_B_PASS_ORDER=count-first LANE_B_OUT="$work/$side" bash research/track-m/lane-b-section16.sh "$tag" > "$work/$side.log" 2>&1
 bun -e 'const r=await Bun.file(process.argv[1]).json();const {events,profile,...brief}=r;const members=events.filter(e=>e.phase==="member-premises"),rows=events.filter(e=>e.phase==="row-premises");console.log(JSON.stringify({side:process.argv[2],...brief,memberPremiseEvents:members.length,memberPremiseTuples:members.reduce((n,e)=>n+(e.added?.length??0),0),rowPremiseEvents:rows.length,rowPremiseTuples:rows.reduce((n,e)=>n+(e.added?.length??0),0)}))' "$work/$side/$tag/summary.json" "$side"
 echo "INPUT=$tag-$side.json.gz" | tee -a "$work/audit.log"
 bun research/track-m/audit-lane-b-cost.ts "$work/$side/$tag/capture.json.gz" replays/family.json | tee -a "$work/audit.log"
 echo "VARIANT_END $variant $tag $side"
done
