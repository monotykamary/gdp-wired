#!/usr/bin/env bash
set -euo pipefail
order=${1:?order}
printf '%s  %s\n' f14f538ea14763ced6f8aac5227ae9bc9fbc6dd18acea4f150cbaadd3eeca639 lane-e-rows/family.json | sha256sum -c -
bash lane-e-preflight/apply.sh
bash lane-e-demand/apply.sh
bash lane-e-flags/apply.sh
bash row-guard/apply.sh
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/inv1758-field-demand-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
cp core/count-recovery/derivability-closure.ts "$work/control-closure.txt"
cp lane-e-rows/family.json "$work/family.json"
cp lane-e-rows/provenance.json "$work/provenance.json"
if test "$order" = check; then
 LAB_DISPOSABLE=1 bun row-field-demand/install-field-demand.ts
 bun run check
 bun test core/count-recovery/field-count-demand.test.ts core/count-recovery/field-demand.integration.test.ts core/count-recovery/derivability-closure.test.ts core/count-recovery/field-bound-lemmas.test.ts core/count-recovery/guard-cases.test.ts core/count-focus-proof.test.ts
 exit
fi
sides='before after'; test "$order" != after || sides='after before'
for side in $sides; do
 cp "$work/control-closure.txt" core/count-recovery/derivability-closure.ts
 if test "$side" = after; then LAB_DISPOSABLE=1 bun row-field-demand/install-field-demand.ts; fi
 sha256sum core/count-recovery/derivability-closure.ts > "$work/$side-source.sha256"
 LANE_B_EARLY_FOCUS=only LANE_B_PASS_ORDER=count-first GDP_COUNTS_TRACE=2 GDP_COUNTS_DUMP_ALL_PASSES=1 GDP_COUNTS_DUMP_MIN=0 GDP_COUNTS_DUMP_N=100000 bun research/track-m/lane-b-cost.ts "$work/family.json" rows "$work/$side" 2700 4800 > "$work/$side.log" 2>&1
 SIDE="$side" bun -e 'const r=await Bun.file(process.argv[1]).json();const {events,last,profile,...small}=r;console.log(JSON.stringify({side:process.env.SIDE,...small,last:last&&{phase:last.phase,pass:last.pass,error:last.error},eventCount:events.length,profile}))' "$work/$side/summary.json"
done
