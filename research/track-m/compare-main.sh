#!/usr/bin/env bash
# Every new paired gate uses approved main, never a flag-disabled Track M tree.
set -euo pipefail
id="$1"; first="$2"; root="$PWD"; base="${TMPDIR:-/tmp}/track-m-approved-main-$$"
trap 'rm -rf "$base"' EXIT
(cd baseline-input && sha256sum -c main.tar.sha256)
revision=$(< baseline-input/revision.txt)
[[ "$revision" == 6a3874d3* ]] || { echo 'wrong approved-main baseline'; exit 2; }
mkdir -p "$base"; tar xf baseline-input/main.tar -C "$base"
bun install --frozen-lockfile >/dev/null 2>&1
(cd "$base" && bun install --frozen-lockfile >/dev/null 2>&1)
unset GDP_ROWS_SHARED GDP_SOURCE_CONTEXTS GDP_SOURCE_INDEX GDP_ROWS_UNWEIGHTED GDP_COUNTS_SHARED_TREES GDP_COUNTS_FOCUS
export GDP_COUNT_LEMMA_CUTS=0
other=base; [ "$first" = base ] && other=cand
failed=0
for phase in search broken; do
  skip=broken; [ "$phase" = broken ] && skip=search
  for side in "$first" "$other"; do
    dir="$root"; [ "$side" = base ] && dir="$base"
    echo "PAIR begin side=$side phase=$phase id=$id baseline=$revision"
    set +e
    (cd "$dir" && timeout -s KILL 60s bun research/protocols/ic3syn/run.ts --ms 60000 --only "$id" --skip "$skip") >"/tmp/track-m-main-pair-$$.out" 2>"/tmp/track-m-main-pair-$$.err"
    status=$?
    set -e
    cat "/tmp/track-m-main-pair-$$.out"
    if [ "$status" -ne 0 ] && [ "$status" -ne 124 ] && [ "$status" -ne 137 ]; then
      tail -c 2000 "/tmp/track-m-main-pair-$$.err"; failed=1
    fi
    echo "PAIR end side=$side phase=$phase exit=$status"
  done
done
rm -f "/tmp/track-m-main-pair-$$.out" "/tmp/track-m-main-pair-$$.err"
exit "$failed"
