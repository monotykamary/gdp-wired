#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/lane-f-core-first-XXXXXX")
trap 'status=$?; bash research/track-m/pack-section18-archive.sh "$work"; exit "$status"' EXIT
install_source(){ cp "$1" "$work/install.txt"; mv "$work/install.txt" "$2"; }
install_source triangle-counts.txt core/counts.ts
install_source triangles-after.txt core/count-write-frames.ts
bun -e 'import{unpack}from"./research/track-m/section18-codec.ts";const{p}=unpack(await Bun.file("context.json").text());await Bun.write(process.argv[1],JSON.stringify(p))' "$work/packet.json"
for side in "$1" "$([[ "$1" == before ]] && echo after || echo before)"; do
 install_source source-projection-base.txt core/count-recovery/derivability-closure.ts
 if [[ "$side" == after ]]; then LAB_DISPOSABLE=1 bun research/track-m/lane-f-core-first-variant.ts; fi
 echo "CORE_FIRST_BEGIN $side"
 sha256sum family.json core/counts.ts core/count-write-frames.ts core/count-recovery/derivability-closure.ts
 timeout 20s bun research/track-m/lane-f-closure.ts "$work/packet.json" 0 "$work/$side" > "$work/$side.log" 2>&1
 tail -n 1 "$work/$side.log"
 echo "CORE_FIRST_END $side"
done
