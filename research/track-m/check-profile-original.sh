#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
LAB_DISPOSABLE=1 bun research/track-m/install-check-cost-profile.ts
out=$(mktemp -d "$HOME/track-m-check-original-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$out"' EXIT
set +e
CHECK_PROFILE_OUT="$out/check-profile.json" GDP_COUNTS_TRACE=123 timeout -s TERM -k 5 70 bun --preload ./research/track-m/check-profile-exit.ts research/protocols/ic3syn/run.ts --ms 60000 --only mldr --skip broken > "$out/run.log" 2>&1
status=$?
echo "STRICT_EXIT=$status"
tail -c 18000 "$out/run.log"
[[ "$status" == 0 || "$status" == 124 ]]
