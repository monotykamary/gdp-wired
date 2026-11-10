#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
bash research/track-m/prepare-vendors.sh
# Reuse prepared dependencies whenever present; one preparation for both modes.
if [[ ! -d node_modules/typescript ]]; then bun install --frozen-lockfile >/dev/null; fi
work=$(mktemp -d /tmp/section13-entry-profile-XXXXXX)
out=$(mktemp -d "$HOME/track-m-entry-profile-XXXXXX"); mkdir -p "$work/frozen"
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
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-entry-profile.ts > "$out/instrumentation-profile.json"
bun -e 'const fs=require("node:fs"),crypto=require("node:crypto"),before=JSON.parse(fs.readFileSync(process.argv[1],"utf8"));const changed=Object.keys(before).filter(p=>crypto.createHash("sha256").update(fs.readFileSync(p)).digest("hex")!==before[p]);if(changed.some(p=>p.startsWith("kernel/")))throw new Error("kernel drift");console.log(JSON.stringify({kernelIdentical:true,changedForInstrumentation:changed}))' "$out/source-before.json" > "$out/integrity.json"
bun -e 'const p=JSON.parse(await Bun.file(process.argv[1]).text());await Bun.write(process.argv[2],JSON.stringify({m:p.m,laws:p.laws}))' "$root/runtime/star.packet.json" "$out/input.json"
bun build research/track-m/run-entry-profile.ts --target=bun --outfile "$out/profile.js" > "$out/build.log" 2>&1
DIAG_OUTPUT=1 timeout -s KILL 180 bun "$out/profile.js" production "$out/input.json" "$out" > "$out/production.log" 2>&1
timeout -s KILL 180 bun "$out/profile.js" deadline-free "$root/runtime/star.packet.json" "$out" > "$out/deadline-free.log" 2>&1
# The profile's two compact records retain the interrupted rows/goal, not columns.
rm -f "$out/profile.js" "$out/input.json"
