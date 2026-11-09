#!/usr/bin/env bash
set -euo pipefail
mode=${1:-original}
order=${2:-candidate-first}
only=${3:-}
base=$(mktemp -d)
trap 'rm -rf "$base"' EXIT
mkdir -p "$base/tree"
tar --exclude=./node_modules --exclude=./baseline --exclude=./.git --exclude=./runs -cf - . | tar -xf - -C "$base/tree"
ln -s "$PWD/node_modules" "$base/tree/node_modules"
cp -R baseline/core/. "$base/tree/core/"
root=$PWD
run_one() {
  local name=$1 dir=$2 code=0
  if [[ $mode == generation ]]; then
    (cd "$dir" && bun research/track-gen/t13-generation.ts "$only") > "$base/$name.log"
  else
    (cd "$dir" && GDP_COUNTS_TRACE=123 GDP_COUNTS_PROF=1 /usr/bin/time -f "STRICT_PROCESS_SECONDS $name %e EXIT %x" timeout -s KILL 60 bun research/protocols/ic3syn/run.ts --ms 60000 --only mldr --skip broken) > "$base/$name.log" 2>&1 || code=$?
    printf '%s\n' "$code" > "$base/$name.code"
  fi
}
if [[ $order == baseline-first ]]; then run_one baseline "$base/tree"; run_one candidate "$root"; else run_one candidate "$root"; run_one baseline "$base/tree"; fi
if [[ $mode == generation ]]; then
  bun research/track-gen/t13-compare.ts "$base/baseline.log" "$base/candidate.log"
else
  echo '=== BASELINE ==='; tail -c 180000 "$base/baseline.log"
  read -r code < "$base/baseline.code"; echo "T13_EXIT baseline $code"
  echo '=== CANDIDATE ==='; tail -c 180000 "$base/candidate.log"
  read -r code < "$base/candidate.code"; echo "T13_EXIT candidate $code"
  [[ $code == 0 ]]
fi
