#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check
bun test research/track-m/{without-deadlines,bounded-research}.test.ts
work=$(mktemp -d /tmp/section13-prepare-XXXXXX)
out="$work/results"; mkdir -p "$out" "$work/frozen"
trap 's=$?; shopt -s nullglob; files=("$out"/*); if ((${#files[@]})); then bun "$root/research/track-m/pack-section10-archive.ts" "${files[@]}"; fi; rm -rf "$work"; exit "$s"' EXIT
(cd source-input && sha256sum -c archive.sha256)
tar xzf source-input/source.tar.gz -C "$work/frozen"
cp -a research/track-m/. "$work/frozen/research/track-m/"
ln -s "$root/node_modules" "$work/frozen/node_modules"; ln -s "$root/vendor" "$work/frozen/vendor"
cd "$work/frozen"
bun research/track-m/section12-integrity.ts before "$out/source-before.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section10-diagnostic.ts family > "$out/instrumentation-base.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section12-unlimited.ts > "$out/instrumentation-ops.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section13-shards.ts > "$out/instrumentation-shards.json"
TRACK_M_SHARDS=1 bun research/track-m/section12-integrity.ts after "$out/source-before.json" > "$out/integrity.json"
bun research/track-m/capture-section13.ts "$root/replay-input/input.json" "$out" > "$out/capture.log"
bun build research/track-m/section13-shard.ts --target=bun --outfile "$out/runtime.js" > "$out/build.log" 2>&1
(cd "$out" && sha256sum runtime.js *.packet.json > runtime.sha256)
