#!/usr/bin/env bash
set -euo pipefail
mkdir -p parent/research/track-gen
tar -xf replay-input/parent.tar -C parent
cp research/track-gen/{probe,profile,meter,install-profile}.ts parent/research/track-gen/
bun install --frozen-lockfile >/dev/null
(cd parent && bun install --frozen-lockfile >/dev/null)
root=$PWD
for prefix in 'one primary' Inv3915 Inv1758 Inv2973 'Inv*'; do
  for side in parent candidate; do
    dir=$root; [[ $side == parent ]] && dir=$root/parent
    echo "PROBE side=$side prefix=$prefix"
    (cd "$dir" && taskset -c 0-3 timeout -s KILL 60 bun research/track-gen/probe.ts "$root/replay-input/input.json" "$prefix")
  done
done
