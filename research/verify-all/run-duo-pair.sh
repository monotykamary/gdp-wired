#!/usr/bin/env bash
# Same VM, fresh processes, alternating order; baseline is a git archive of 6a3874d3.
set -eu
id=$1; rep=$2; root=$PWD
mkdir -p /tmp/verify-base
tar -xf verify-base-data/base.tar -C /tmp/verify-base
(cd /tmp/verify-base && bun install --frozen-lockfile >/dev/null)
bun install --frozen-lockfile >/dev/null
cpus=$(python3 -c 'import os; print(",".join(map(str,sorted(os.sched_getaffinity(0))[:4])))')
echo "PAIR_META id=$id repeat=$rep cpus=$cpus"
sha256sum kernel/kernel.ts /tmp/verify-base/kernel/kernel.ts
order='cand base'; if [ "$((rep % 2))" -eq 0 ]; then order='base cand'; fi
for side in $order; do
  dir=$root; if [ "$side" = base ]; then dir=/tmp/verify-base; fi
  echo "PAIR begin side=$side id=$id run=$rep"
  set +e
  (cd "$dir" && /usr/bin/time -f 'PAIR_WALL seconds=%e exit=%x' taskset -c "$cpus" timeout -s KILL 60 bun research/protocols/run.ts --ms 60000 --only "$id" --skip given,broken)
  s=$?
  set -e
  echo "PAIR end side=$side exit=$s"
done
