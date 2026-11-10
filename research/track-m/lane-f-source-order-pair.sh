#!/usr/bin/env bash
set -euo pipefail
[[ $# -eq 3 ]]
case "$1" in closure|original) ;; *) exit 2 ;; esac
case "$2" in compensated|ready-empty) ;; *) exit 2 ;; esac
case "$3" in before|after) ;; *) exit 2 ;; esac
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/lane-f-source-order-XXXXXX")
trap 'status=$?; bash research/track-m/pack-section18-archive.sh "$work"; exit "$status"' EXIT
install_source(){ cp "$1" "$work/install.txt"; mv "$work/install.txt" "$2"; }
install_source triangle-counts.txt core/counts.ts
if [[ "$1" == closure ]]; then bun -e 'import{unpack}from"./research/track-m/section18-codec.ts";const{p}=unpack(await Bun.file("context.json").text());await Bun.write(process.argv[1],JSON.stringify(p))' "$work/packet.json"; fi
for side in "$3" "$([[ "$3" == before ]] && echo after || echo before)"; do
 install_source source-projection-base.txt core/count-recovery/derivability-closure.ts
 LAB_DISPOSABLE=1 bun research/track-m/lane-f-scalar-source-variant.ts
 LAB_DISPOSABLE=1 bun research/track-m/lane-f-source-cdcl-variant.ts
 LAB_DISPOSABLE=1 bun research/track-m/lane-f-prefer-compensated-variant.ts
 if [[ "$side" == after ]]; then LAB_DISPOSABLE=1 bun research/track-m/lane-f-source-order-variant.ts "$2"; fi
 echo "SOURCE_ORDER_BEGIN $1 $2 $side"
 sha256sum family.json core/counts.ts core/count-write-frames.ts core/count-recovery/derivability-closure.ts
 if [[ "$1" == closure ]]; then
  timeout 20s bun research/track-m/lane-f-closure.ts "$work/packet.json" 0 "$work/$side" > "$work/$side.log" 2>&1
 else
  timeout 20s bun research/track-m/lane-b-cost.ts family.json overlap "$work/$side" 6000 7000 > "$work/$side.log" 2>&1
 fi
 tail -n 1 "$work/$side.log"
 echo "SOURCE_ORDER_END $1 $2 $side"
done
