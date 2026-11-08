#!/usr/bin/env bash
# Matched, strict-60s original-harness runs. Installation is not timed.
set -euo pipefail
id="$1"; first="$2"; root="$PWD"
mkdir -p /tmp/track-m-pair-base
tar xf paired-input/base.tar -C /tmp/track-m-pair-base
base=/tmp/track-m-pair-base
bun install --frozen-lockfile >/dev/null 2>&1
(cd "$base" && bun install --frozen-lockfile >/dev/null 2>&1)
other=base; [ "$first" = base ] && other=cand
failed=0
for phase in search broken; do
  skip=broken; [ "$phase" = broken ] && skip=search
  for side in "$first" "$other"; do
    dir="$root"; [ "$side" = base ] && dir="$base"
    echo "PAIR begin side=$side phase=$phase id=$id"
    set +e
    (cd "$dir" && taskset -c 0-3 timeout -s KILL 60 bun research/protocols/ic3syn/run.ts --ms 60000 --only "$id" --skip "$skip") >/tmp/track-m-pair.out 2>/tmp/track-m-pair.err
    status=$?
    set -e
    cat /tmp/track-m-pair.out
    if [ "$status" -ne 0 ] && [ "$status" -ne 124 ] && [ "$status" -ne 137 ]; then
      tail -c 2000 /tmp/track-m-pair.err
      failed=1
    fi
    echo "PAIR end side=$side phase=$phase exit=$status"
  done
done
exit "$failed"
