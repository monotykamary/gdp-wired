#!/usr/bin/env bash
set -euo pipefail
root="$PWD"; packets=$(mktemp -d /tmp/section19-packets-XXXXXX); trap 'rm -rf "$packets"' EXIT; mv runtime/* "$packets/"; rmdir runtime
bash research/track-m/prepare-vendors.sh
if [[ ! -d node_modules/typescript ]]; then bun install --frozen-lockfile >/dev/null; fi
bun run check
bun test research/track-m/section18.test.ts research/track-m/section19.test.ts
work=$(mktemp -d /tmp/section19-build-XXXXXX); out=$(mktemp -d "$HOME/track-m-section19-XXXXXX"); mkdir -p "$work/frozen"
trap 's=$?; bash "$root/research/track-m/pack-section18-archive.sh" "$out" || s=1; rm -rf "$work" "$packets"; exit "$s"' EXIT
(cd source-input && sha256sum -c archive.sha256); tar xzf source-input/source.tar.gz -C "$work/frozen"
cp -a research/track-m/. "$work/frozen/research/track-m/"; ln -s "$root/node_modules" "$work/frozen/node_modules"; ln -s "$root/vendor" "$work/frozen/vendor"; cd "$work/frozen"
bun research/track-m/section12-integrity.ts before "$out/before.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section18.ts > "$out/instrumentation.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section19.ts > "$out/citation-instrumentation.json"
bun -e 'import{readFileSync}from"node:fs";import{createHash}from"node:crypto";const before=JSON.parse(readFileSync(process.argv[1],"utf8")),changed=Object.keys(before).filter(p=>createHash("sha256").update(readFileSync(p)).digest("hex")!==before[p]),allowed=["core/count-cases.ts","core/count-recovery/field-bound-lemmas.ts","core/count-recovery/frame-lemmas.ts","core/count-recovery/derivability-closure.ts","core/count-recovery/conditional-proof.ts","core/count-recovery/ops.ts","core/count-recovery/guard-cases.ts","core/count-select.ts"];if(changed.some(p=>!allowed.includes(p)))throw Error("unexpected core/kernel mutation");console.log(JSON.stringify({kernelIdentical:true,changed}))' "$out/before.json" > "$out/integrity.json"
bun build research/track-m/section19-run.ts --target=bun --outfile "$out/replay.js" > "$out/build.log" 2>&1
sha256sum "$out/replay.js" > "$out/runtime.sha256"
for spec in overlap:0 overlap:4 star:3 star:5; do
 law="${spec%:*}"; op="${spec#*:}"
 for mode in observe; do
  timeout -s KILL 130 bun "$out/replay.js" "$packets/$law.packet.json" "$op" "$out/$law-op$op-$mode" "$mode" > "$out/$law-op$op-$mode.log" 2>&1
 done
 done
