#!/usr/bin/env bash
set -euo pipefail
mode=${1:?mode}; order=${2:?order}
if test "$order" != check; then
 test -f lane-e-rows/family.json
 test -f lane-e-rows/provenance.json
 printf '%s  %s\n' f14f538ea14763ced6f8aac5227ae9bc9fbc6dd18acea4f150cbaadd3eeca639 lane-e-rows/family.json | sha256sum -c -
fi
bash lane-e-preflight/apply.sh
bash lane-e-demand/apply.sh
bash lane-e-flags/apply.sh
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/inv1758-guard-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
cp core/counts.ts "$work/control-counts.txt"
cp core/count-recovery/member-inclusions.ts "$work/control-member.txt"
cp row-guard/member-inclusions.after.txt "$work/candidate-member.txt"
if test "$order" = check; then
 bash row-guard/apply.sh
 if test "$mode" != plain; then LAB_DISPOSABLE=1 bun row-early/install-early.ts "$mode"; fi
 bun run check
 bun test core/count-recovery/member-inclusions.test.ts core/count-recovery/member-premises.test.ts core/count-witness-flags.test.ts core/count-focused.test.ts core/count-recovery/empty-count-source.test.ts core/count-ranges.test.ts core/finite-tiny.test.ts core/finite-tiny-houdini.test.ts core/count-completion.test.ts
 exit
fi
cp lane-e-rows/family.json "$work/family.json"
cp lane-e-rows/provenance.json "$work/provenance.json"
sides='before after'; test "$order" != after || sides='after before'
for side in $sides; do
 cp "$work/control-counts.txt" core/counts.ts
 cp "$work/control-member.txt" core/count-recovery/member-inclusions.ts
 if test "$side" = after; then
  bash row-guard/apply.sh
  if test "$mode" != plain; then LAB_DISPOSABLE=1 bun row-early/install-early.ts "$mode"; fi
 fi
 sha256sum core/counts.ts core/count-recovery/member-inclusions.ts > "$work/$side-source.sha256"
 code=0
 LANE_B_PASS_ORDER=count-first GDP_COUNTS_TRACE=2 GDP_COUNTS_DUMP_ALL_PASSES=1 GDP_COUNTS_DUMP_MIN=0 GDP_COUNTS_DUMP_N=100000 bun research/track-m/lane-b-cost.ts "$work/family.json" rows "$work/$side" 2700 4800 > "$work/$side.log" 2>&1 || code=$?
 if test -f "$work/$side/summary.json"; then
  SIDE="$side" bun -e 'const r=await Bun.file(process.argv[1]).json();const {events,last,profile,...small}=r;console.log(JSON.stringify({side:process.env.SIDE,...small,last:last&&{phase:last.phase,pass:last.pass,error:last.error},eventCount:events.length,profile}))' "$work/$side/summary.json"
 else tail -c 3000 "$work/$side.log"; fi
 if test "$code" != 0; then exit "$code"; fi
done
