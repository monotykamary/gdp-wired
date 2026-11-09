#!/usr/bin/env bash
# Same-VM Lane B policy comparison on the imported A/E/F source. Not a gate.
set -euo pipefail
tag=$1; first=${2:-before}
[[ "$first" == before || "$first" == after ]]
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/track-m-b-integrated-$tag-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
files=(core/count-cases.ts core/count-recovery/{guard-cases,field-bound-lemmas,row-cases,derivability-closure,field-demand}.ts)
for file in "${files[@]}"; do mkdir -p "$work/base/$(dirname "$file")"; cp "$file" "$work/base/$file"; done
sha256sum replays/family.json > "$work/family.sha256"
for side in "$first" "$([[ "$first" == before ]] && echo after || echo before)"; do
 for file in "${files[@]}"; do cp "$work/base/$file" "$file"; done
 echo "LANE_B_PAIR_BEGIN $tag $side"
 set +e
 if [[ "$side" == after ]]; then
  LANE_B_OUT="$work/$side" LEAF_VARIANT=after DERIVE_VARIANT=after bash research/track-m/lane-b-section16.sh "$tag" > "$work/$side.log" 2>&1
 else
  LANE_B_OUT="$work/$side" bash research/track-m/lane-b-section16.sh "$tag" > "$work/$side.log" 2>&1
 fi
 status=$?
 set -e
 sha256sum "${files[@]}" > "$work/$side.sha256"
 if [[ -f "$work/$side/$tag/summary.json" ]]; then
  bun -e 'const [file,side]=process.argv.slice(1),r=await Bun.file(file).json();const {events,profile,...brief}=r;console.log(JSON.stringify({side,...brief}))' "$work/$side/$tag/summary.json" "$side"
 else
  tail -n 15 "$work/$side.log"
 fi
 echo "LANE_B_PAIR_END $tag $side EXIT=$status"
 [[ "$status" == 0 ]] || exit "$status"
done
