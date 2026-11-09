#!/usr/bin/env bash
set -euo pipefail
mode=$1; variant=${2:-after}; target=${3:-safety}
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
if [[ "$mode" == check ]]; then
 bun run check
 bun test core/count-completion.test.ts core/count-recovery/field-demand.test.ts core/count-recovery/guard-cases.test.ts core/count-recovery/field-bound-budget.test.ts core/count-recovery/leaf-allowance.test.ts
 exit
fi
LAB_DISPOSABLE=1 bun research/track-m/lane-b-variant.ts "$variant"
out=$(mktemp -d "$HOME/track-m-lane-b-$mode-$variant-$target-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$out"' EXIT
if [[ "$mode" == capture ]]; then
 set +e
 DUMP_DIR="$out/dump" DUMP_ALL=1 DUMP_MIN=0 DUMP_N=100000 GDP_COUNTS_TRACE=123 timeout -s KILL 60 bun --preload ./research/query/dump.ts --preload ./research/track-m/lane-b-trace.ts research/protocols/ic3syn/run.ts --ms 60000 --only mldr --skip broken > "$out/run.log" 2>&1
 status=$?
 echo "STRICT_EXIT=$status"
 tail -c 12000 "$out/run.log"
 [[ "$status" == 0 || "$status" == 124 || "$status" == 137 ]]
else
 if [[ -n "${FAMILY_JSON:-}" ]]; then cp "$FAMILY_JSON" "$out/family.json"; else bun research/track-m/lane-b-family.ts "$out/family.json"; fi
 DUMP_DIR="$out/dump" DUMP_ALL=1 DUMP_MIN=0 DUMP_N=100000 bun --preload ./research/query/dump.ts --preload ./research/track-m/lane-b-trace.ts research/track-m/lane-b-cost.ts "$out/family.json" "$target" "$out/$target" 2700
fi
