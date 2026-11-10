#!/usr/bin/env bash
set -euo pipefail
root="$PWD"; base="${TMPDIR:-/tmp}/mldr-repair-$$"; mkdir -p "$base"
trap 'rm -rf "$base"' EXIT
unset GDP_COUNTS_FOCUS GDP_ROWS_SHARED GDP_SOURCE_CONTEXTS GDP_SOURCE_INDEX GDP_ROWS_UNWEIGHTED GDP_COUNTS_SHARED_TREES
export GDP_COUNT_LEMMA_CUTS=0
for rev in 844a1baf 844a1baf-deferred; do
 dir="$base/$rev"; mkdir -p "$dir"; tar xf bisect-input/main.tar -C "$dir"
 (cd "$dir" && git apply "$root/bisect-input/$rev.patch" && bun install --frozen-lockfile >/dev/null 2>&1)
 cp research/track-m/probe-ordinary-mldr.ts "$dir/research/track-m/probe-ordinary-mldr.ts"
 for law in 'one primary' Inv3915; do
  echo "MLDR_BEGIN revision=$rev law=$law route=focused"
  (cd "$dir" && timeout -s KILL 60s bun research/track-m/profile-production.ts focused "$root/replay-input/input.json" "$law") | tee "$base/focused.jsonl"
  bun -e 'const r=(await Bun.file(process.argv[1]).text()).split("\n").filter(l=>l.startsWith("{")).map(JSON.parse).at(-1);if(!r?.proven||!r?.checked)throw Error("complete MLDR law was not checked");' "$base/focused.jsonl"
  echo "MLDR_BEGIN revision=$rev law=$law route=ordinary"
  (cd "$dir" && timeout -s KILL 60s bun research/track-m/probe-ordinary-mldr.ts "$root/replay-input/input.json" "$law")
 done
done
