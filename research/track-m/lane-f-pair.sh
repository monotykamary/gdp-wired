#!/usr/bin/env bash
set -euo pipefail
kind=$1; tag=$2; op=${3:-0}; order=${4:-before}
sha256sum -c SHA256SUMS
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/lane-f-pair-XXXXXX")
trap 'status=$?; if [[ $status -ne 0 ]]; then for log in "$work"/*.log; do [[ -f "$log" ]] && tail -n 25 "$log"; done; fi; bash research/track-m/pack-section18-archive.sh "$work"; exit "$status"' EXIT
mkdir -p "$work/control"
tar xzf controls.tar.gz -C "$work/control"
for f in core/count-cases.ts core/count-recovery/{row-cases,derivability-closure,field-bound-lemmas,frame-lemmas,conditional-proof,guard-cases,field-demand}.ts; do mkdir -p "$work/candidate/$(dirname "$f")"; cp "$f" "$work/candidate/$f"; done
if [[ "$kind" != family ]]; then
 mkdir -p "$work/capture" packets
 tar xzf "archives/$tag.tar.gz" -C "$work/capture"
 bun research/track-m/lane-f-freeze.ts "$work/capture" "$tag" packets
fi
for side in "$order" "$([[ "$order" == before ]] && echo after || echo before)"; do
 for f in core/count-cases.ts core/count-recovery/{row-cases,derivability-closure,field-bound-lemmas,frame-lemmas,conditional-proof,guard-cases,field-demand}.ts; do
  if [[ "$side" == before && -f "$work/control/$f" ]]; then cp "$work/control/$f" "$f"; else cp "$work/candidate/$f" "$f"; fi
 done
 if [[ "${CLASS_FIRST:-0}" == 1 ]]; then
  LAB_DISPOSABLE=1 bun research/track-m/section15-leaf-variant.ts after
  LAB_DISPOSABLE=1 bun research/track-m/section15-derive-variant.ts after
 fi
 echo "LANE_F_BEGIN $kind $tag $op $side"
 for f in core/count-cases.ts core/count-recovery/{row-cases,derivability-closure}.ts; do sha256sum "$f"; done
 if [[ "$kind" == op ]]; then
  LAB_DISPOSABLE=1 bun research/track-m/install-lane-b-op.ts
  timeout -s KILL 20 bun research/track-m/lane-f-op.ts "packets/$tag.packet.json" "$op" "$work/$side" > "$work/$side.log" 2>&1
 elif [[ "$kind" == closure ]]; then
  timeout -s KILL 20 bun research/track-m/lane-f-closure.ts "packets/$tag.packet.json" "$op" "$work/$side" > "$work/$side.log" 2>&1
 else
  timeout -s KILL 20 bun research/track-m/lane-b-cost.ts replays/family.json "$tag" "$work/$side" 6000 7000 > "$work/$side.log" 2>&1
 fi
 tail -n 1 "$work/$side.log"
 echo "LANE_F_END $kind $tag $op $side"
done
