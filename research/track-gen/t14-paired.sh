#!/usr/bin/env bash
set -euo pipefail
mode=${1:?mode}
id=${2:?protocol}
repeat=${3:-1}
base_kind=${4:-main}
root=$PWD
printf 'T14_CPU_MODEL %s\n' "$(awk -F ' : |: ' '/^model name/{print $2; exit}' /proc/cpuinfo)"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
base="$scratch/base"
mkdir -p "$base"
tar -xf "baselines/$base_kind.tar" -C "$base"
mkdir -p "$base/vendor" "$base/research/track-gen"
cp -R "$root/vendor/." "$base/vendor/"
cp "$root/research/track-gen/t13-generation.ts" "$root/research/track-gen/t14-measure.ts" "$base/research/track-gen/"
bun install --frozen-lockfile >/dev/null
(cd "$base" && bun install --frozen-lockfile >/dev/null)
failed=0
run_one() {
  local side=$1 dir=$2 code=0
  local -a preload=(--preload ./research/track-gen/t14-measure.ts)
  if [[ $side == candidate && ${T14_CAPTURE:-0} == 1 ]]; then
    mkdir -p "$scratch/capture"
    export DUMP_DIR="$scratch/capture" DUMP_ALL=1 DUMP_N=10000 GDP_COUNTS_DUMP_ALL_PASSES=1 GDP_COUNTS_DUMP_N=100
    preload+=(--preload ./research/query/dump.ts --preload ./research/track-gen/t14-dump.ts)
  fi
  if [[ $mode == generation ]]; then
    (cd "$dir" && bun research/track-gen/t13-generation.ts "$id") > "$scratch/$side.log" 2> "$scratch/$side.err" || code=$?
  else
    local script=research/protocols/ic3syn/run.ts skip=broken
    [[ $mode == duoai ]] && script=research/protocols/run.ts && skip=broken,given
    [[ $mode == broken ]] && skip=search
    (cd "$dir" && GDP_INFER_TRACE=2 /usr/bin/time -f "STRICT_PROCESS_SECONDS $side %e EXIT %x" timeout -s KILL 60 bun "${preload[@]}" "$script" --ms 60000 --only "$id" --skip "$skip") > "$scratch/$side.log" 2> "$scratch/$side.err" || code=$?
  fi
  echo "PAIR begin side=$side id=$id repeat=$repeat mode=$mode"
  cat "$scratch/$side.log"
  tail -c 60000 "$scratch/$side.err"
  echo "PAIR end side=$side exit=$code"
  if (( code != 0 )); then failed=1; fi
  return 0
}
if (( repeat % 2 )); then run_one candidate "$root"; run_one baseline "$base"; else run_one baseline "$base"; run_one candidate "$root"; fi
if (( failed )); then exit 1; fi
if [[ $mode == generation ]]; then bun research/track-gen/t13-compare.ts "$scratch/baseline.log" "$scratch/candidate.log"; fi
