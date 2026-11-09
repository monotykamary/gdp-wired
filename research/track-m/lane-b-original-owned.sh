#!/usr/bin/env bash
# Capture an actual original-harness admission family, then measure owned helpers.
set -euo pipefail
rep=${1:?repeat}
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
out=$(mktemp -d "$HOME/track-m-original-owned-$rep-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$out"' EXIT
cp replays/family.json "$out/frozen-family.json"
cp core/counts.ts "$out/counts.before.ts"
sha256sum core/counts.ts kernel/kernel.ts kernel/prove.ts research/protocols/ic3syn/run.ts > "$out/source.before.sha256"
LAB_DISPOSABLE=1 bun research/track-m/install-lane-b-original-family.ts
sha256sum core/counts.ts > "$out/source.observed.sha256"
ORIGINAL_FAMILY_OUT="$out" FROZEN_FAMILY="$out/frozen-family.json" timeout -s KILL 75 bun --preload ./research/track-m/capture-lane-b-original-family.ts research/protocols/ic3syn/run.ts --ms 60000 --only mldr --skip broken > "$out/generation.log" 2>&1
test -s "$out/family.json"
cp "$out/counts.before.ts" core/counts.ts
sha256sum core/counts.ts kernel/kernel.ts kernel/prove.ts research/protocols/ic3syn/run.ts > "$out/source.restored.sha256"
cmp "$out/source.before.sha256" "$out/source.restored.sha256"
cp "$out/family.json" replays/family.json
printf 'ORIGINAL_FAMILY %s\n' "$rep"
bun -e 'console.log(JSON.stringify(await Bun.file(process.argv[1]).json()))' "$out/family-comparison.json"
LAB_DISPOSABLE=1 bun research/track-m/install-check-cost-profile.ts
while IFS= read -r tag; do
 [[ -n "$tag" ]] || continue
 LANE_B_OUT="$out/owned" bash research/track-m/lane-b-section16.sh "$tag" > "$out/$tag.log" 2>&1
 bun -e 'const r=await Bun.file(process.argv[1]).json();const {events,profile,...brief}=r;console.log(JSON.stringify({repeat:process.argv[2],...brief}))' "$out/owned/$tag/summary.json" "$rep"
done < "$out/owned-targets.txt"
