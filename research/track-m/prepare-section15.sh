#!/usr/bin/env bash
set -euo pipefail
root="$PWD"; bash research/track-m/prepare-vendors.sh
if [[ ! -d node_modules/typescript ]]; then bun install --frozen-lockfile >/dev/null; fi
bun run check
bun test research/track-m/section15.test.ts
work=$(mktemp -d /tmp/section15-build-XXXXXX); out=$(mktemp -d "$HOME/track-m-section15-XXXXXX"); mkdir -p "$work/frozen"
trap 's=$?; bun "$root/research/track-m/pack-section10-archive.ts" "$out"/*; rm -rf "$work"; exit "$s"' EXIT
(cd source-input && sha256sum -c archive.sha256); tar xzf source-input/source.tar.gz -C "$work/frozen"
cp -a research/track-m/. "$work/frozen/research/track-m/"; ln -s "$root/node_modules" "$work/frozen/node_modules"; ln -s "$root/vendor" "$work/frozen/vendor"; cd "$work/frozen"
bun research/track-m/section12-integrity.ts before "$out/source-before.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section10-diagnostic.ts family > "$out/diagnostic.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section12-unlimited.ts > "$out/ledger.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section13-shards.ts > "$out/shard.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section15.ts > "$out/policy.json"
bun -e 'import {readFileSync,readdirSync,statSync} from "node:fs";import{createHash}from"node:crypto";const list=p=>readdirSync(p).flatMap(n=>statSync(p+"/"+n).isDirectory()?list(p+"/"+n):[p+"/"+n]);const before=JSON.parse(readFileSync(process.argv[1],"utf8")),after=Object.fromEntries(["core","kernel"].flatMap(list).map(p=>[p,createHash("sha256").update(readFileSync(p)).digest("hex")])),changed=Object.keys(after).filter(p=>after[p]!==before[p]),allowed=["core/count-cases.ts","core/count-focus-proof.ts","core/count-recovery/derivability-closure.ts","core/count-recovery/guard-cases.ts"];if(changed.some(p=>!allowed.includes(p))||Object.keys(after).length!==Object.keys(before).length)throw new Error("unexpected mutation");console.log(JSON.stringify({revision:"5974b916",kernelIdentical:true,changed,after}))' "$out/source-before.json" > "$out/integrity.json"
bun build research/track-m/section15-run.ts --target=bun --outfile "$out/replay.js" > "$out/build.log" 2>&1
sha256sum "$out/replay.js" > "$out/runtime.sha256"
for spec in overlap:4 overlap:0 star:3; do
 law="${spec%:*}"; op="${spec#*:}"
 timeout -s KILL 650 bun "$out/replay.js" "$root/runs/track-m/section15-runtime/$law.packet.json" "$op" "$out/$law-op$op" all > "$out/$law-op$op.log" 2>&1
 done
