#!/usr/bin/env bash
# One original strict harness process per revision, same exclusive VM; no taskset.
set -euo pipefail
root="$PWD"; base="${TMPDIR:-/tmp}/paxos-revision-$$"; mkdir -p "$base"
trap 'rm -rf "$base"' EXIT
unset GDP_ROWS_SHARED GDP_SOURCE_CONTEXTS GDP_SOURCE_INDEX GDP_ROWS_UNWEIGHTED GDP_COUNTS_SHARED_TREES GDP_COUNTS_FOCUS
export GDP_COUNT_LEMMA_CUTS=0
for rev in "$@"; do
  dir="$base/$rev"
  if [ ! -d "$dir" ]; then
    mkdir -p "$dir"; tar xf "$root/bisect-input/main.tar" -C "$dir"
    if [ -s "$root/bisect-input/$rev.patch" ]; then (cd "$dir" && git apply "$root/bisect-input/$rev.patch"); fi
    (cd "$dir" && bun install --frozen-lockfile >"$base/install-$rev.log" 2>&1) || { tail -c 3000 "$base/install-$rev.log"; exit 2; }
  fi
  for repeat in $(seq 1 "${PAXOS_REPEATS:-1}"); do
    echo "REVISION_BEGIN revision=$rev repeat=$repeat"
    start=$(date +%s%N)
    set +e
    (cd "$dir" && timeout -s KILL 60s bun research/protocols/ic3syn/run.ts --ms 60000 --only paxos_epr --skip broken) >"$base/out.jsonl" 2>"$base/err.log"
    rc=$?
    set -e
    end=$(date +%s%N)
    bun "$root/research/track-m/paxos-revision-result.ts" "$rev" "$repeat" "$rc" "$start" "$end" "$base/out.jsonl"
    if [ "$rc" -ne 0 ]; then tail -c 2000 "$base/err.log"; fi
  done
done
