#!/usr/bin/env bash
set -euo pipefail
root="$PWD"; bash research/track-m/prepare-vendors.sh
if [[ ! -d node_modules/typescript ]]; then bun install --frozen-lockfile >/dev/null; fi
work=$(mktemp -d /tmp/section14-build-XXXXXX); out=$(mktemp -d "$HOME/track-m-section14-build-XXXXXX"); mkdir -p "$work/frozen"
trap 's=$?; bun "$root/research/track-m/pack-section10-archive.ts" "$out"/*; rm -rf "$work"; exit "$s"' EXIT
(cd source-input && sha256sum -c archive.sha256); tar xzf source-input/source.tar.gz -C "$work/frozen"
cp -a research/track-m/. "$work/frozen/research/track-m/"; ln -s "$root/node_modules" "$work/frozen/node_modules"; ln -s "$root/vendor" "$work/frozen/vendor"; cd "$work/frozen"
bun research/track-m/section12-integrity.ts before "$out/source-before.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section10-diagnostic.ts family > "$out/instrumentation-base.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section12-unlimited.ts > "$out/instrumentation-ledger.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section13-shards.ts > "$out/instrumentation-shards.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section14.ts > "$out/instrumentation-root-seeds.json"
TRACK_M_SHARDS=1 bun research/track-m/section12-integrity.ts after "$out/source-before.json" > "$out/integrity.json"
bun build research/track-m/section14-run.ts --target=bun --outfile "$out/replay.js" > "$out/build.log" 2>&1
bun build research/track-m/section14-prove-roots.ts --target=bun --outfile "$out/roots.js" >> "$out/build.log" 2>&1
(cd "$out" && sha256sum replay.js roots.js > runtime.sha256)
timeout -s KILL 600 bun "$out/replay.js" "$root/runtime/overlap.packet.json" 4 "$out/op4-normal" 50000 > "$out/op4-normal.log" 2>&1
