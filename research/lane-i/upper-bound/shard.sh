#!/usr/bin/env bash
set -euo pipefail
tag=${1:?}; op=${2:?}; pass=${3:?}; ceilings=${4:?}; wall=${5:-1800000}
bash research/lane-i/validate.sh setup
sha256sum -c upper-input/source.sha256
grep -m1 'model name' /proc/cpuinfo
mkdir -p upper-output
LAB_DISPOSABLE=1 bun research/lane-i/upper-bound/install.ts "$ceilings"
set +e
/usr/bin/time -v -o upper-output/time.txt timeout --signal=TERM --kill-after=5s "$((wall / 1000 + 10))s" bun research/lane-i/upper-bound/run.ts upper-input/family.json "$tag" "$op" "$pass" "$ceilings" "$wall"
status=$?
set -e
printf 'UPPER_PROCESS_EXIT %s\n' "$status"
if [[ -s upper-output/proof.json.gz ]]; then
  timeout --signal=TERM --kill-after=5s 120s bun research/lane-i/upper-bound/verify.ts upper-output/proof.json.gz
fi
printf 'UPPER_RESOURCE_BEGIN\n'; if [[ -s upper-output/time.txt ]]; then readarray -t lines < upper-output/time.txt; printf '%s\n' "${lines[@]}"; fi
if [[ ! -s upper-output/result.json && -s upper-output/progress.json ]]; then
  printf 'UPPER_CENSORED '; tr -d '\n' < upper-output/progress.json; printf '\n'
fi
if [[ "$status" != 0 && "$status" != 124 && "$status" != 137 && "$status" != 143 ]]; then exit "$status"; fi
