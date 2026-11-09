#!/usr/bin/env bash
# Same-VM Lane B policy comparison on the imported A/E/F source. Not a gate.
set -euo pipefail
tag=$1; first=${2:-before}; comparison=${3:-combined}
[[ "$comparison" == combined || "$comparison" == isolate ]]
[[ "$first" == before || "$first" == after ]]
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/track-m-b-integrated-$tag-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
files=(core/count-cases.ts core/count-recovery/{guard-cases,field-bound-lemmas,row-cases,derivability-closure,field-demand}.ts)
for file in "${files[@]}"; do mkdir -p "$work/base/$(dirname "$file")"; cp "$file" "$work/base/$file"; done
sha256sum replays/family.json > "$work/family.sha256"
sides=("$first" "$([[ "$first" == before ]] && echo after || echo before)")
if [[ "$comparison" == isolate ]]; then
 if [[ "$first" == before ]]; then sides=(base before after); else sides=(after before base); fi
fi
for side in "${sides[@]}"; do
 for file in "${files[@]}"; do cp "$work/base/$file" "$file"; done
 echo "LANE_B_PAIR_BEGIN $tag $side"
 set +e
 flags=(); policy=base
 case "$comparison:$side" in
  combined:after) flags=(LEAF_VARIANT=after DERIVE_VARIANT=after); policy=combined;;
  isolate:before) flags=(LEAF_VARIANT=after); policy=leaf-only;;
  isolate:after) flags=(DERIVE_VARIANT=after); policy=class-only;;
 esac
 env LANE_B_OUT="$work/$side" "${flags[@]}" bash research/track-m/lane-b-section16.sh "$tag" > "$work/$side.log" 2>&1
 status=$?
 set -e
 sha256sum "${files[@]}" > "$work/$side.sha256"
 if [[ -f "$work/$side/$tag/summary.json" ]]; then
  bun -e 'const [file,side,policy,comparison]=process.argv.slice(1),r=await Bun.file(file).json();const {events,profile,...brief}=r;console.log(JSON.stringify({side,policy,comparison,...brief}))' "$work/$side/$tag/summary.json" "$side" "$policy" "$comparison"
 else
  tail -n 15 "$work/$side.log"
 fi
 echo "LANE_B_PAIR_END $tag $side EXIT=$status"
 [[ "$status" == 0 ]] || exit "$status"
done
