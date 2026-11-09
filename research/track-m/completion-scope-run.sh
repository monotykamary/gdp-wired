#!/usr/bin/env bash
set -euo pipefail
cohort=${1:?}; mode=${2:?}; model=${3:-}
if [[ "$mode" == strict ]] && ! grep -Eq '^model name[[:space:]]*:[[:space:]]*AMD Ryzen 9 9950X 16-Core Processor[[:space:]]*$' /proc/cpuinfo; then
 bun research/track-m/completion-scope-benchmark.ts "$cohort" "$mode"
 exit 0
fi
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
trap 'if [[ -f completion-scope-work.txt ]]; then work=$(<completion-scope-work.txt); bash research/track-m/pack-section18-archive.sh "$work"; fi' EXIT
bun research/track-m/completion-scope-benchmark.ts "$cohort" "$mode" "$model"
