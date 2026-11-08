#!/usr/bin/env bash
set -euo pipefail
mkdir -p parent/research/track-gen
tar -xf replay-input/parent.tar -C parent
cp research/track-gen/{profile,meter,install-profile}.ts parent/research/track-gen/
bun install --frozen-lockfile >/dev/null
(cd parent && bun install --frozen-lockfile >/dev/null)
root=$PWD
for repeat in 1 2 3; do
  sides='parent candidate'; [[ $repeat == 2 ]] && sides='candidate parent'
  for side in $sides; do
    dir=$root; [[ $side == parent ]] && dir=$root/parent
    echo "GENERATION repeat=$repeat side=$side"
    (cd "$dir" && timeout -s KILL 60 bun research/track-gen/profile.ts)
  done
done
for side in parent candidate; do
  dir=$root; [[ $side == parent ]] && dir=$root/parent
  echo "PROFILE side=$side"
  (cd "$dir" && TRACK_GEN_DISPOSABLE=1 bun research/track-gen/install-profile.ts && timeout -s KILL 60 bun research/track-gen/profile.ts)
done
