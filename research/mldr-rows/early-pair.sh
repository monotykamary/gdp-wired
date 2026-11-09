#!/usr/bin/env bash
set -euo pipefail
mode=${1:?mode}; budget=${2:?budget}; order=${3:?order}
bash lane-e-preflight/apply.sh
bash lane-e-demand/apply.sh
bash lane-e-flags/apply.sh
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/inv1758-early-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
cp core/counts.ts "$work/control-counts.txt"
cp lane-e-rows/family.json "$work/family.json"
cp lane-e-rows/provenance.json "$work/provenance.json"
if test "$order" = check; then
 mkdir -p research/mldr-rows
 cp row-early/install-early.ts row-early/install-early.test.ts research/mldr-rows/
 LAB_DISPOSABLE=1 bun research/mldr-rows/install-early.ts "$mode"
 bun run check
 bun test research/mldr-rows/install-early.test.ts core/count-completion.test.ts core/count-recovery/member-premises.test.ts
 exit
fi
wall=4800; test "$budget" != 6000 || wall=7000
sides='before after'; test "$order" != after || sides='after before'
for side in $sides; do
 cp "$work/control-counts.txt" core/counts.ts
 if test "$side" = after; then LAB_DISPOSABLE=1 bun row-early/install-early.ts "$mode"; fi
 sha256sum core/counts.ts > "$work/$side-source.sha256"
 code=0
 LANE_B_PASS_ORDER=count-first GDP_COUNTS_TRACE=2 GDP_COUNTS_DUMP_ALL_PASSES=1 GDP_COUNTS_DUMP_MIN=0 GDP_COUNTS_DUMP_N=100000 bun research/track-m/lane-b-cost.ts "$work/family.json" rows "$work/$side" "$budget" "$wall" > "$work/$side.log" 2>&1 || code=$?
 if test -f "$work/$side/summary.json"; then
  SIDE="$side" bun -e 'const r=await Bun.file(process.argv[1]).json();const {events,last,profile,...small}=r;console.log(JSON.stringify({side:process.env.SIDE,...small,last:last&&{phase:last.phase,pass:last.pass,error:last.error},eventCount:events.length,profile}))' "$work/$side/summary.json"
 else
  tail -c 3000 "$work/$side.log"
 fi
 if test "$code" != 0; then exit "$code"; fi
done
