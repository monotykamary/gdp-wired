#!/usr/bin/env bash
# Research-only composite: exact archived Lane A plus this lane's source patch.
# Not a full gate, not an accepted Git candidate, and no budget modifications.
set -euo pipefail
repeat=${1:?repeat}
mode=${2:-pair}
[[ $mode == pair || $mode == capture ]] || exit 2
root=$PWD
input="$root/incl-integration"
(cd "$input" && sha256sum -c SHA256SUMS)
IFS= read -r source_sha < "$input/A.rev"
[[ "$(git get-tar-commit-id < "$input/A.tar")" == "$source_sha" ]] || { echo "archive revision mismatch"; exit 2; }
printf 'INTEGRATED source A=%s\n' "$source_sha"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
for side in base cand; do
 [[ $mode == capture && $side == base ]] && continue
 mkdir -p "$scratch/$side"
 tar xf "$input/A.tar" -C "$scratch/$side"
 if [[ $side == cand ]]; then
  (cd "$scratch/$side" && git apply --check "$input/E.patch" && git apply "$input/E.patch")
  cp "$input/member-inclusions.ts" "$input/member-inclusions.test.ts" "$scratch/$side/core/count-recovery/"
 fi
 (cd "$scratch/$side" && bash "$root/research/track-m/prepare-vendors.sh" && bun install --frozen-lockfile >/dev/null)
done
(cd "$scratch/cand" && bun test core/count-recovery/member-inclusions.test.ts)
if [[ $mode == capture ]]; then
 order=cand
 mkdir -p "$scratch/cand/research/query" "$scratch/cand/research/track-p"
 cp "$root/research/query/dump.ts" "$scratch/cand/research/query/dump.ts"
 cp "$root/research/track-p/capture.ts" "$scratch/cand/research/track-p/capture.ts"
elif (( repeat % 2 )); then order='base cand'; else order='cand base'; fi
code=0
for side in $order; do
 printf 'INTEGRATED begin side=%s repeat=%s\n' "$side" "$repeat"
 (cd "$scratch/$side" && sha256sum core/counts.ts core/count-support.ts core/count-recovery/member-inclusions.ts 2>/dev/null) || true
 set +e
 if [[ $mode == capture ]]; then
  (cd "$scratch/$side" && DUMP_DIR="$scratch/$side/capture" DUMP_MIN=0 DUMP_N=100000 DUMP_ALL=1 GDP_COUNTS_TRACE=2 timeout -s KILL 75 bun --preload ./research/query/dump.ts --preload ./research/track-p/capture.ts research/protocols/ic3syn/run.ts --only mldr --ms 60000 --skip broken) >"$scratch/result.jsonl" 2>"$scratch/trace.log"
  rc=$?
 else
  (cd "$scratch/$side" && timeout -s KILL 75 bun research/protocols/ic3syn/run.ts --only mldr --ms 60000 --skip broken)
  rc=$?
 fi
 set -e
 if [[ $mode == capture ]]; then
  bun -e 'const f=require("fs");console.log(f.readFileSync(process.argv[1],"utf8"));console.log(f.readFileSync(process.argv[2],"utf8").slice(-4000));' "$scratch/result.jsonl" "$scratch/trace.log"
  bun "$root/research/mldr-incl/pack-capture.ts" "$scratch/$side/capture" 160000
 fi
 printf 'INTEGRATED end side=%s repeat=%s exit=%s\n' "$side" "$repeat" "$rc"
 if ((rc)); then code=$rc; fi
done
exit "$code"
