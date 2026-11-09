#!/usr/bin/env bash
set -euo pipefail
cp -a frozen-paxos/. .
packet=$PWD
root=$(mktemp -d /tmp/lane-i-p1-draft.XXXXXX)
trap 'rm -rf "$root"' EXIT
bun regression-driver/paxos-fix-source.ts "$root"
cp -a draft-overlay/. "$root/"
mkdir -p "$root/research/lane-i-fastloop"
cp regression-driver/p1-tools/*.ts "$root/research/lane-i-fastloop/"
cd "$root"
bun install --frozen-lockfile >/dev/null
sha256sum core/counts.ts core/counts-completion-order.test.ts scripts/test-shards.ts
set +e
bun run check
check=$?
bun test core/counts-completion-order.test.ts core/count-completion.test.ts core/count-recovery-order.test.ts research/lane-i/regressions/p1-scheduling-audit.test.ts
tests=$?
bun scripts/test-shards.ts --list >/dev/null
roster=$?
set -e
out=$(mktemp -d "$root/p1-proof.XXXXXX")
LANE_B_PASS_ORDER=count-first LANE_B_EARLY_FOCUS=off bun research/lane-i-fastloop/lane-b-cost.ts "$packet/p1-input/family.json" p1 "$out" 6000 7000 > "$out/driver.log"
bun research/lane-i-fastloop/audit-lane-b-cost.ts "$out/capture.json.gz" "$packet/p1-input/family.json" > "$out/audit.json"
bun -e 'import{readFileSync}from"node:fs";import{gunzipSync,gzipSync}from"node:zlib";const d=process.argv[1],s=JSON.parse(readFileSync(d+"/summary.json","utf8")),a=JSON.parse(readFileSync(d+"/audit.json","utf8")),p=JSON.parse(gunzipSync(readFileSync(d+"/capture.json.gz")).toString());delete p.captures;console.log("P1_DRAFT_MEASURE "+JSON.stringify({checked:s.checked,units:s.units,wallMs:s.wallMs,nativeReplay:a.checked}));console.log("P1_DRAFT_PROOF_GZIP "+gzipSync(JSON.stringify(p)).toString("base64"));if(!s.withinDiagnosticLine||!a.checked||Math.abs(s.units-1152.3382236)>1e-6)throw Error("p1 old-cost criterion failed")' "$out"
set +e
timeout -s KILL 60 bun research/protocols/ic3syn/run.ts --ms 60000 --only paxos_epr --skip broken > "$root/whole.log" 2>&1
whole=$?
set -e
bun -e 'import{readFileSync}from"node:fs";const t=readFileSync(process.argv[1],"utf8"),rows=t.split("\n").flatMap(l=>{try{return[JSON.parse(l)]}catch{return[]}}).filter(r=>r.id==="paxos_epr");console.log("P1_DRAFT_WHOLE "+JSON.stringify({exit:Number(process.argv[2]),rows}));if(Number(process.argv[2])||rows.length!==1||rows[0].search?.verdict!=="proven"||rows[0].search.work!==6915544||rows[0].search.full!==1037946)throw Error("whole Paxos baseline-work criterion failed")' "$root/whole.log" "$whole"
printf 'P1_DRAFT_CHECKS check=%s tests=%s roster=%s whole=%s\n' "$check" "$tests" "$roster" "$whole"
[[ "$check" == 0 && "$tests" == 0 && "$roster" == 0 && "$whole" == 0 ]]
