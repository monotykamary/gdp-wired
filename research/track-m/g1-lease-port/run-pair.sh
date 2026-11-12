#!/usr/bin/env bash
set -euo pipefail
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
arm=${PORT_PAIR_ARM:?}
[[ $arm == 0 || $arm == 1 ]]
# Remove inherited GDP switches before setting the exact same base in both arms.
for key in ${!GDP_@}; do unset "$key"; done
export GDP_WORK_FULL=1 GDP_WORK_STEPS=0 GDP_CYCLIC_LOG=0
export GDP_COUNT_CLOSING_RESERVE=1 GDP_COUNT_FINAL_DEFER_CHECKS=1 GDP_COUNT_FRAMES=1 GDP_COUNT_LIFTED=1 GDP_COUNT_LIFTED_PREREQUISITES=1 GDP_COUNT_LIFTED_REPLACEMENT=1 GDP_COUNT_PREREQUISITES=1 GDP_COUNT_REJECTIONS=1 GDP_COUNT_ROW_DEFER_CHECKS=1 GDP_COUNT_STRATEGIES=1 GDP_COUNT_TIERS=1 GDP_REQUEST_QUOTIENT=1
export GDP_COUNT_C2_LEMMAS=0 GDP_COUNT_EMITTER_FRAME_POOL=0
export GDP_COUNT_DEFER_CHECKS=$arm GDP_COUNT_C2_REPLAY=$arm
bun=/home/user/.bun/bin/bun
[[ $("$bun" --version) == 1.4.3 ]]
[[ $(sha256sum "$bun" | cut -d ' ' -f 1) == 7ce7d6b654eddeec20afddf2396317fba6dc19ab52788a27e894e1806bf8f24b ]]
"$bun" install --frozen-lockfile > "$out/install.log" 2>&1
bash research/track-m/prepare-vendors.sh > "$out/vendors.log" 2>&1
"$bun" research/track-m/g1-lease-port/construct.ts g1-input/family.json "$out" > "$out/construct.log" 2>&1
"$bun" research/track-m/g1-lease-port/replay.ts "$out/family.json" --mutations > "$out/native.log" 2>&1
printf 'PASS: lease construction; 95321; native 19/38; four mutations\n' > "$out/result.txt"
