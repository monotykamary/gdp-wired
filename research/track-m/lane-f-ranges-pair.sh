#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/lane-f-ranges-XXXXXX")
trap 'status=$?; if [[ $status -ne 0 ]]; then for f in "$work"/*.log; do [[ -f "$f" ]] && tail -n 8 "$f"; done; fi; bash research/track-m/pack-section18-archive.sh "$work"; exit "$status"' EXIT
cp core/counts.ts "$work/candidate.txt"
sha256sum family.json before-counts.txt
for side in "$1" "$([[ "$1" == before ]] && echo after || echo before)"; do
 if [[ "$side" == before ]]; then cp before-counts.txt core/counts.ts; else cp "$work/candidate.txt" core/counts.ts; fi
 echo "RANGE_PAIR_BEGIN $side"
 sha256sum core/counts.ts
 timeout 20s bun research/track-m/lane-b-cost.ts family.json overlap "$work/$side" 6000 7000 > "$work/$side.log" 2>&1
 tail -n 1 "$work/$side.log"
 echo "RANGE_PAIR_END $side"
done
