#!/usr/bin/env bash
# Untouched original harness, paired engine sources, not an admission snapshot.
set -euo pipefail
rep=${1:?repeat}; first=${2:?before or after}
[[ "$first" == before || "$first" == after ]]
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
out=$(mktemp -d "$HOME/track-m-original-completion-$rep-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$out"' EXIT
cp replays/control-counts.ts "$out/before-counts.ts"
cp core/counts.ts "$out/after-counts.ts"
failed=0
for side in "$first" "$([[ "$first" == before ]] && echo after || echo before)"; do
 cp "$out/$side-counts.ts" core/counts.ts
 sha256sum core/counts.ts core/count-ranges.ts kernel/kernel.ts kernel/prove.ts research/protocols/ic3syn/run.ts > "$out/$side.sha256"
 set +e
 GDP_INFER_TRACE=2 GDP_COUNTS_TRACE=123 timeout -s TERM -k 5 70 bun research/protocols/ic3syn/run.ts --ms 60000 --only mldr --skip broken > "$out/$side.log" 2>&1
 status=$?
 set -e
 [[ "$status" == 0 ]] || failed=1
 bun -e 'const [file,repeat,side,exit]=process.argv.slice(1),text=await Bun.file(file).text(),rows=text.split("\n").flatMap(line=>{try{return[JSON.parse(line)]}catch{return[]}}),record=rows.find(r=>r.id==="mldr");console.log(JSON.stringify({scope:"original-harness",repeat:Number(repeat),side,harnessExit:Number(exit),strictProven:Number(exit)===0&&record?.search?.verdict==="proven"&&record.search.ms<=60000,record}));' "$out/$side.log" "$rep" "$side" "$status"
done
[[ "$failed" == 0 ]]
