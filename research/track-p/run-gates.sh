#!/usr/bin/env bash
# Lightweight local coordinator only; all checks and benchmark workers run on boat.
set -euo pipefail
revision=${1:?committed candidate required}
base=${2:-/tmp/gdp-track-p-main-40693c7}
out=${3:-runs/track-p-final-gates}
run_stage() {
  local stage=$1 jobs=$2 expected=$3
  shift 3
  echo "GATE_BEGIN=$stage"
  supercomputer run --jobs "$jobs" --out "$out/$stage" --class gate --vm-type large "$@"
  bun -e 'const [file,n]=process.argv.slice(1),s=(await Bun.file(file).text()).trim().split("\n").filter(Boolean).map(x=>x.split(/\s+/));if(s.length!==Number(n)||s.some(x=>Number(x[1])!==0))throw Error("incomplete or failed stage: "+file);console.log("STAGE_RECEIPTS_OK="+file)' "$out/$stage/summary.tsv" "$expected"
}
run_stage check research/track-p/final-check-jobs.json 1
run_stage strict research/track-p/strict-repeat-jobs.json 3
bun -e 'const root=process.argv[1];for(let i=1;i<=3;i++){const t=await Bun.file(`${root}/paxos-r${i}.log`).text(),r=t.split("\n").filter(l=>l.startsWith("{")).map(JSON.parse).find(r=>r.id==="paxos_epr");if(r?.search?.verdict!=="proven"||r.search.ms>60000||!t.includes("STRICT_EXIT=0"))throw Error("strict target failed "+i);console.log(JSON.stringify({strict:i,ms:r.search.ms,verdict:r.search.verdict}));}' "$out/strict"
run_stage ic3syn-paired research/track-p/ic3syn-paired-gate-jobs.json 87 --data "$base:base"
bun research/track-p/summarize-gates.ts "$out" --ic3syn
run_stage duoai-paired research/track-p/duoai-paired-gate-jobs.json 10 --data "$base:base"
bun research/track-p/summarize-gates.ts "$out" --pairs
run_stage broken research/track-p/broken-gate-jobs.json 29
run_stage shard research/track-p/shard-gate-jobs.json 7
bun research/track-p/summarize-gates.ts "$out"
echo GATE_BEGIN=quick-bar
bun gates/bar.ts --cand "$revision" --base 40693c7a2e9adcae77c6558dedb8278bd5704ce7 --quick --backend boat --name "track-p-final-${revision:0:8}"
echo GATE_WORKERS_FINISHED=1
