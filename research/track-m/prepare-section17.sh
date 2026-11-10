#!/usr/bin/env bash
set -euo pipefail
root="$PWD"; bash research/track-m/prepare-vendors.sh
if [[ ! -d node_modules/typescript ]]; then bun install --frozen-lockfile >/dev/null; fi
bun run check
bun test research/track-m/section17.test.ts
work=$(mktemp -d /tmp/section17-build-XXXXXX); out=$(mktemp -d "$HOME/track-m-section17-XXXXXX"); mkdir -p "$work/baseline"
trap 's=$?; bun "$root/research/track-m/pack-section10-archive.ts" "$out"/*; rm -rf "$work"; exit "$s"' EXIT
(cd source-input && sha256sum -c archive.sha256); tar xzf source-input/source.tar.gz -C "$work/baseline"
cp -a research/track-m/. "$work/baseline/research/track-m/"
ln -s "$root/node_modules" "$work/baseline/node_modules"; ln -s "$root/vendor" "$work/baseline/vendor"
(cd "$work/baseline" && bun research/track-m/section12-integrity.ts before "$out/before.json" && TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section17.ts observe > "$out/observe.json" && bun build research/protocols/ic3syn/run.ts --target=bun --outfile "$out/baseline.js" > "$out/baseline-build.log" 2>&1)
cp -a "$work/baseline" "$work/pool"
(cd "$work/pool" && TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section17.ts pool > "$out/pool-policy.json" && bun build research/protocols/ic3syn/run.ts --target=bun --outfile "$out/pool.js" > "$out/pool-build.log" 2>&1)
cp -a "$work/pool" "$work/combo"
(cd "$work/combo" && TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section17.ts combo > "$out/combo-policy.json" && bun build research/protocols/ic3syn/run.ts --target=bun --outfile "$out/combo.js" > "$out/combo-build.log" 2>&1)
bun -e 'import{readFileSync,readdirSync,statSync,writeFileSync}from"node:fs";import{createHash}from"node:crypto";const [work,out]=process.argv.slice(1),walk=p=>readdirSync(p).flatMap(n=>statSync(p+"/"+n).isDirectory()?walk(p+"/"+n):[p+"/"+n]),before=JSON.parse(readFileSync(out+"/before.json","utf8")),rows=[];for(const mode of["baseline","pool","combo"]){const dir=work+"/"+mode,changed=Object.keys(before).filter(p=>createHash("sha256").update(readFileSync(dir+"/"+p)).digest("hex")!==before[p]),allowed=["core/counts.ts",...(mode==="combo"?["core/count-cases.ts","core/count-recovery/guard-cases.ts","core/count-recovery/derivability-closure.ts"]:[])];if(changed.some(p=>!allowed.includes(p)))throw Error("unexpected core/kernel change");rows.push({mode,kernelIdentical:true,changed,bundleSha256:createHash("sha256").update(readFileSync(out+"/"+mode+".js")).digest("hex")})}writeFileSync(out+"/integrity.json",JSON.stringify(rows,null,2)+"\n")' "$work" "$out"
bun research/track-m/section17-run.ts "$out"
