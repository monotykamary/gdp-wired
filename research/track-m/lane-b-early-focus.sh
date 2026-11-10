#!/usr/bin/env bash
set -euo pipefail
tag=${1:?target}; mode=${2:?off third or only}; policy=${3:-base}
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/track-m-early-$tag-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
# Isolate scheduling from the separate range-fix experiment.
tar xf replays/control.tar
cp replays/family.json "$work/family.json"
sha256sum replays/family.json > "$work/family.sha256"
if [[ "$policy" == classes ]]; then
 LAB_DISPOSABLE=1 bun research/track-m/section15-leaf-variant.ts helpers
 LAB_DISPOSABLE=1 bun research/track-m/section15-derive-variant.ts after
fi
sha256sum core/counts.ts core/count-focus-proof.ts core/count-cases.ts core/count-recovery/{guard-cases,field-bound-lemmas,row-cases,derivability-closure,field-demand}.ts > "$work/source.sha256"
LANE_B_EARLY_FOCUS="$mode" LANE_B_PASS_ORDER=count-first LANE_B_OUT="$work/run" GDP_COUNTS_DUMP_ALL_PASSES=1 GDP_COUNTS_TRACE=2 GDP_COUNTS_PROF=1 bash research/track-m/lane-b-section16.sh "$tag" > "$work/run.log" 2>&1
bun -e 'const r=await Bun.file(process.argv[1]).json();const {events,profile,...brief}=r;console.log(JSON.stringify(brief))' "$work/run/$tag/summary.json"
