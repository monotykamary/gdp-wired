#!/usr/bin/env bash
set -euo pipefail
mode=${1:-generation}
order=${2:-candidate-first}
base=$(mktemp -d)
trap 'rm -rf "$base"' EXIT
# node_modules may be mounted on another device. Copy only source, and share
# dependencies read-only through a symlink; never hardlink across mount points.
mkdir -p "$base/tree"
tar --exclude=./node_modules --exclude=./baseline --exclude=./.git --exclude=./runs -cf - . | tar -xf - -C "$base/tree"
ln -s "$PWD/node_modules" "$base/tree/node_modules"
for file in counts.ts exists.ts field-laws.ts; do cp "baseline/core/$file" "$base/tree/core/$file"; done
root=$PWD
run_one() {
  local name=$1 dir=$2
  if [[ $mode == generation ]]; then
    (cd "$dir" && bun research/track-gen/t13-generation.ts) > "$base/$name.log"
  else
    (cd "$dir" && GDP_COUNTS_TRACE=123 GDP_COUNTS_PROF=1 bun research/protocols/ic3syn/run.ts --ms 60000 --only mldr --skip broken) > "$base/$name.log" 2>&1
  fi
}
if [[ $order == baseline-first ]]; then run_one baseline "$base/tree"; run_one candidate "$root"; else run_one candidate "$root"; run_one baseline "$base/tree"; fi
if [[ $mode == generation ]]; then
  bun research/track-gen/t13-compare.ts "$base/baseline.log" "$base/candidate.log"
else
  echo '=== BASELINE ==='; tail -c 180000 "$base/baseline.log"
  echo '=== CANDIDATE ==='; tail -c 180000 "$base/candidate.log"
fi
