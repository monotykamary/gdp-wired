#!/usr/bin/env bash
# Conditional Inv1758 baseline on the exact fresh 34-law family; no supplied laws.
set -euo pipefail
budget=${1:?budget}; wall=${2:?wall}; order=${3:?order}
bash lane-e-preflight/apply.sh
bash lane-e-demand/apply.sh
bash lane-e-flags/apply.sh
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/inv1758-baseline-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
cp lane-e-rows/family.json "$work/family.json"
cp lane-e-rows/provenance.json "$work/provenance.json"
sha256sum core/counts.ts core/count-ranges.ts core/count-recovery/member-premises.ts > "$work/source.sha256"
bun -e 'import{createHash}from"node:crypto";const p=await Bun.file("lane-e-rows/provenance.json").json(),t=await Bun.file("lane-e-rows/family.json").text();if(createHash("sha256").update(t).digest("hex")!==p.inputSha256)throw Error("input hash");console.log(JSON.stringify({inputVerified:true,...p}))'
code=0
LANE_B_PASS_ORDER="$order" GDP_COUNTS_TRACE=2 GDP_COUNTS_DUMP_ALL_PASSES=1 GDP_COUNTS_DUMP_MIN=0 GDP_COUNTS_DUMP_N=100000 bun research/track-m/lane-b-cost.ts "$work/family.json" rows "$work/result" "$budget" "$wall" > "$work/run.log" 2>&1 || code=$?
if test -f "$work/result/summary.json"; then
 bun -e 'const r=await Bun.file(process.argv[1]).json();const {events,profile,checkProfile,cache,last,...small}=r;console.log(JSON.stringify({...small,last:last&&{phase:last.phase,pass:last.pass,goal:last.goal,error:last.error},eventCount:events.length,stages:events.map(e=>({phase:e.phase,pass:e.pass,hyps:e.hyps})),profile,cache,checkProfile}))' "$work/result/summary.json"
else
 echo MISSING_SUMMARY
 tail -c 4000 "$work/run.log"
fi
exit "$code"
