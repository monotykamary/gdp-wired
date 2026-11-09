#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
LAB_DISPOSABLE=1 bun research/track-m/lane-b-share-variant.ts "$1"
out=$(mktemp -d "$HOME/track-m-lane-b-share-$1-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$out"' EXIT
set +e
GDP_COUNTS_TRACE=3 timeout -s KILL 60 bun research/protocols/ic3syn/run.ts --ms 60000 --only mldr --skip broken > "$out/run.log" 2>&1
status=$?
echo "STRICT_EXIT=$status"
tail -c 15000 "$out/run.log"
[[ "$status" == 0 || "$status" == 124 || "$status" == 137 ]]
