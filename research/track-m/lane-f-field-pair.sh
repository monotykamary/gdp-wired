#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/lane-f-field-XXXXXX")
trap 'status=$?; if [[ $status -ne 0 ]]; then for f in "$work"/*.log; do [[ -f "$f" ]] && tail -n 8 "$f"; done; fi; bash research/track-m/pack-section18-archive.sh "$work"; exit "$status"' EXIT
cp source-projection-base.txt "$work/source.txt"
if [[ "$1" == closure ]]; then bun -e 'import{unpack}from"./research/track-m/section18-codec.ts";const{p}=unpack(await Bun.file("context.json").text());await Bun.write(process.argv[1],JSON.stringify(p))' "$work/packet.json"; fi
for side in "$2" "$([[ "$2" == before ]] && echo after || echo before)"; do
 cp "$work/source.txt" "$work/install.txt"
 mv "$work/install.txt" core/count-recovery/derivability-closure.ts
 if [[ "$side" == after ]]; then LAB_DISPOSABLE=1 bun "research/track-m/lane-f-${VARIANT:-field-projection}-variant.ts"; fi
 echo "FIELD_PAIR_BEGIN $1 $side"
 sha256sum core/count-recovery/derivability-closure.ts
 if [[ "$1" == closure ]]; then timeout 20s bun research/track-m/lane-f-closure.ts "$work/packet.json" 0 "$work/$side" > "$work/$side.log" 2>&1; else timeout 20s bun research/track-m/lane-b-cost.ts family.json overlap "$work/$side" 6000 7000 > "$work/$side.log" 2>&1; fi
 tail -n 1 "$work/$side.log"
 echo "FIELD_PAIR_END $1 $side"
done
