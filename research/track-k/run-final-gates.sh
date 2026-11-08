#!/usr/bin/env bash
# Controller only: substantive work is submitted to boat; local Bun calls read completed receipts.
set -euo pipefail
cd "$(dirname "$0")/../.."
root=$PWD
version=${1:-v1}
from=${2:-ic3syn}
[[ "$version" =~ ^[a-zA-Z0-9_-]+$ ]] || { echo "Invalid output version" >&2; exit 2; }
case "$from" in ic3syn|duoai|broken|shards|bar) ;; *) echo "Unknown gate: $from" >&2; exit 2 ;; esac
active=0
export GIT_EDITOR=true EDITOR=true
for stage in ic3syn duoai broken shards bar; do
  [ "$stage" = "$from" ] && active=1
  [ "$active" -eq 1 ] || continue
  echo "GATE begin $stage"
  case "$stage" in
    ic3syn)
      out="runs/track-k-final-ic3syn-$version"
      supercomputer run --jobs research/track-k/final-ic3syn-jobs.json --out "$out" --class gate --urgent --vm-type large --vms 4 --data runs/track-k-main-8610af26:base
      bun research/track-k/check-gates.ts paired "$out"
      ;;
    duoai)
      out="runs/track-k-final-duoai-$version"
      supercomputer run --jobs research/track-k/final-duoai-jobs.json --out "$out" --class gate --vm-type large --vms 4 --data runs/track-k-main-8610af26:base
      bun research/track-k/check-gates.ts paired "$out"
      ;;
    broken)
      out="runs/track-k-final-broken-$version"
      supercomputer run --jobs research/track-k/final-broken-jobs.json --out "$out" --class gate --vm-type large --vms 4
      bun research/track-k/check-gates.ts broken "$out"
      ;;
    shards)
      out="runs/track-k-final-shards-$version"
      supercomputer run --jobs research/track-k/final-shard-jobs.json --out "$out" --class gate --vm-type large --vms 4
      bun research/track-k/check-gates.ts shards "$out"
      ;;
    bar)
      export GDPW_BAR_DIR="$root/runs/track-k-bar"
      bun gates/bar.ts --quick --together --base 8610af26 --cand 0e9afc3d --backend boat --name "track-k-$version" --procs 6 > "runs/track-k-bar-$version.log" 2>&1
      bun research/track-k/check-bar.ts "$GDPW_BAR_DIR/runs/track-k-$version"
      ;;
  esac
  echo "GATE passed $stage"
done
