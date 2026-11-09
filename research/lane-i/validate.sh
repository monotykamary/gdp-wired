#!/usr/bin/env bash
set -euo pipefail
mode=${1:?}; repeat=${2:-1}; id=${3:-mldr}
prepare_vendor() {
  local target=$1
  for v in handwired gdp-ts; do
    mkdir -p "$target/vendor/$v"
    tar -xf "integ-input/$v.tar" -C "$target/vendor/$v"
  done
}
(cd integ-input && sha256sum -c SHA256SUMS)
prepare_vendor .
bun install --frozen-lockfile >/dev/null
if [[ "$mode" == setup ]]; then exit 0; fi
mkdir -p base
tar -xf integ-input/main.tar -C base
prepare_vendor base
(cd base && bun install --frozen-lockfile >/dev/null)
mkdir -p base/research/lane-i
cp research/lane-i/timing.ts base/research/lane-i/timing.ts
cp integ-input/identity.json identity.json
cat identity.json
grep -m1 'model name' /proc/cpuinfo
sides='base candidate'; if [[ "$repeat" == 2 ]]; then sides='candidate base'; fi
for side in $sides; do
  dir=.; if [[ "$side" == base ]]; then dir=base; fi
  echo "LANE_I_BEGIN $mode $repeat $id $side"
  if [[ "$mode" == census ]]; then
    mkdir -p "$dir/research/track-gen"
    if [[ "$side" == base ]]; then cp research/track-gen/t13-generation.ts "$dir/research/track-gen/t13-generation.ts"; fi
    (cd "$dir" && timeout -s KILL "${LANE_I_CENSUS_SECONDS:-120}" bun research/track-gen/t13-generation.ts "$id") > "$side.out" 2> "$side.err"
    cat "$side.err"
  else
    set +e
    (cd "$dir" && GDP_COUNTS_TRACE=3 GDP_INFER_TRACE=2 timeout -s KILL 60 bun --preload ./research/lane-i/timing.ts research/protocols/ic3syn/run.ts --ms 60000 --only "$id" --skip broken) > "$side.out" 2> "$side.err"
    code=$?
    set -e
    echo "LANE_I_EXIT $side $code"
    cat "$side.out" "$side.err"
    if [[ "$code" != 0 && "$code" != 124 && "$code" != 137 ]]; then exit "$code"; fi
  fi
  echo "LANE_I_END $mode $repeat $id $side"
done
if [[ "$mode" == census ]]; then bun research/lane-i/census-compare.ts "$id" "$repeat" base.out candidate.out; fi
