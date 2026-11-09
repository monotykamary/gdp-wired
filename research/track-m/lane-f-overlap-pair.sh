#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/lane-f-overlap-XXXXXX")
trap 'status=$?; if [[ $status -ne 0 ]]; then for f in "$work"/*.log; do [[ -f "$f" ]] && tail -n 8 "$f"; done; fi; bash research/track-m/pack-section18-archive.sh "$work"; exit "$status"' EXIT
cp core/count-recovery/boolean-core.ts "$work/boolean-core.ts"
sha256sum family.json
for side in "$1" "$([[ "$1" == before ]] && echo after || echo before)"; do
 cp "$work/boolean-core.ts" core/count-recovery/boolean-core.ts
 if [[ "$side" == after ]]; then LAB_DISPOSABLE=1 bun research/track-m/lane-f-selector-variant.ts; fi
 echo "OVERLAP_PAIR_BEGIN $side"
 sha256sum core/count-recovery/boolean-core.ts
 timeout 20s bun research/track-m/lane-b-cost.ts family.json overlap "$work/$side" 6000 7000 > "$work/$side.log" 2>&1
 tail -n 1 "$work/$side.log"
 echo "OVERLAP_PAIR_END $side"
done
