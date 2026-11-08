#!/usr/bin/env bash
# Isolate row sharing in the exact same post-merge production source.
set -euo pipefail
id="$1"; first="$2"
bun install --frozen-lockfile >/dev/null 2>&1
other=base; [ "$first" = base ] && other=cand
failed=0
for phase in search broken; do
  skip=broken; [ "$phase" = broken ] && skip=search
  for side in "$first" "$other"; do
    rows=1; [ "$side" = base ] && rows=0
    echo "PAIR begin side=$side phase=$phase id=$id"
    set +e
    GDP_ROWS_SHARED="$rows" GDP_COUNT_LEMMA_CUTS=0 taskset -c 0-3 timeout -s KILL 60 bun research/protocols/ic3syn/run.ts --ms 60000 --only "$id" --skip "$skip" >/tmp/track-m-pair.out 2>/tmp/track-m-pair.err
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
