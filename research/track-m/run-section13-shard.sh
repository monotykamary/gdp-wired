#!/usr/bin/env bash
set -euo pipefail
label="$1"; op="$2"; work=$(mktemp -d /tmp/section13-shard-XXXXXX)
out="$work/results"; mkdir -p "$out"
trap 'rm -rf "$work"' EXIT
(cd runtime && sha256sum -c runtime.sha256)
set +e
timeout -s KILL 600 bun runtime/runtime.js "runtime/$label.packet.json" "$op" "$out" > "$out/search.log" 2>&1
status=$?
set -e
if [[ ! -f "$out/result.json" ]]; then bun research/track-m/finish-section13-censored.ts "$out" "runtime/$label.packet.json" "$op" "$status"; fi
bun -e 'const x=JSON.parse(await Bun.file(process.argv[1]).text());delete x.trace;delete x.columns;console.log(JSON.stringify({shardResult:x}))' "$out/result.json"
bun research/track-m/pack-section10-archive.ts "$out"/*
