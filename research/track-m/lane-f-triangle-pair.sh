#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/lane-f-triangle-XXXXXX")
trap 'status=$?; if [[ $status -ne 0 ]]; then for f in "$work"/*.log; do [[ -f "$f" ]] && tail -n 8 "$f"; done; fi; bash research/track-m/pack-section18-archive.sh "$work"; exit "$status"' EXIT
install_source(){ cp "$1" "$work/install.txt"; mv "$work/install.txt" "$2"; }
install_source triangle-counts.txt core/counts.ts
install_source source-projection-base.txt core/count-recovery/derivability-closure.ts
sha256sum family.json core/counts.ts core/count-recovery/derivability-closure.ts
if [[ "$1" == closure ]]; then bun -e 'import{unpack}from"./research/track-m/section18-codec.ts";const{p}=unpack(await Bun.file("context.json").text());await Bun.write(process.argv[1],JSON.stringify(p))' "$work/packet.json"; fi
for side in "$2" "$([[ "$2" == before ]] && echo after || echo before)"; do
 install_source "triangles-$side.txt" core/count-write-frames.ts
 install_source source-projection-base.txt core/count-recovery/derivability-closure.ts
 if [[ "$side" == after && "${SOURCE_DEMAND:-0}" == 1 ]]; then LAB_DISPOSABLE=1 bun research/track-m/lane-f-source-demand-variant.ts; fi
 install_source triangle-counts.txt core/counts.ts
 if [[ "$side" == after && "${INITIAL_TRANSPORT:-0}" == 1 ]]; then LAB_DISPOSABLE=1 bun research/track-m/lane-f-initial-transport-variant.ts; fi
 echo "TRIANGLE_PAIR_BEGIN $1 $side"
 sha256sum core/count-write-frames.ts core/count-recovery/derivability-closure.ts
 if [[ "$1" == closure ]]; then timeout 20s bun research/track-m/lane-f-closure.ts "$work/packet.json" 0 "$work/$side" > "$work/$side.log" 2>&1; else timeout 20s bun research/track-m/lane-b-cost.ts family.json overlap "$work/$side" 6000 7000 > "$work/$side.log" 2>&1; fi
 tail -n 1 "$work/$side.log"
 echo "TRIANGLE_PAIR_END $1 $side"
done
