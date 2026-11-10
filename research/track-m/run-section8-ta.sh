#!/usr/bin/env bash
# Ordered T-A only. No production implementation or subsequent Section 8 tests.
set -euo pipefail
work=$(mktemp -d /tmp/section8-ta-XXXXXX)
trap 'rm -rf "$work"' EXIT
bun research/track-m/section8-ta-data.ts followup-input/t2-hygiene.log prior-input/active-source.json | tee "$work/ta-data.log"
empty=$(bun -e 'import {readFileSync} from "node:fs";const r=readFileSync(process.argv[1],"utf8").split("\n").filter(l=>l.startsWith("{")).map(l=>JSON.parse(l));if(r.length!==2)throw new Error("missing T-A data");console.log(r.some(r=>r.empty===true)?"yes":"no")' "$work/ta-data.log")
if [[ "$empty" == yes ]]; then
 echo "T-A stop: empty recorded violated set"
 bun research/track-m/pack-section7-receipts.ts "$work/ta-data.log"
 exit 0
fi
echo "T-A setup: pinned vendors"
timeout -s KILL 120 bash research/track-m/prepare-vendors.sh
echo "T-A setup: dependencies"
timeout -s KILL 120 bun install --frozen-lockfile >/dev/null
echo "T-A setup: parse/build research observer"
bun build research/track-m/section8-ta-observer.ts --target bun --outdir "$work/smoke" >/dev/null
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section8-ta.ts
export LAB_DEMAND_PROPOSALS=1 LAB_SOURCE_MS=5000 LAB_SOURCE_TRACE=1 LAB_CONDITIONAL_PROOF=1
export LAB_SECTION7_CAPTURE=v7-input/demand-and-sources.log LAB_SECTION7_MEASUREMENT=T2 LAB_SECTION7_CLEAN_WITNESSES=1
for law in 'Inv*' Inv2973; do
 if [[ -n "${LAB_SECTION8_ONLY:-}" && "$law" != "$LAB_SECTION8_ONLY" ]]; then continue; fi
 if [[ "$law" == 'Inv*' ]]; then file=ta-star.log; else file=ta-overlap.log; fi
 timeout -s KILL 90 bun research/track-m/active-source-probe.ts replay-input/input.json "$law" 5 all > "$work/$file"
 stop=$(bun -e 'import {readFileSync} from "node:fs";const r=readFileSync(process.argv[1],"utf8").split("\n").filter(l=>l.startsWith("{")).map(l=>JSON.parse(l)).find(r=>r.test==="T-A");if(!r)throw new Error("missing T-A result");console.log(r.stop?"yes":"no")' "$work/$file")
 if [[ "$stop" == yes ]]; then
  echo 'T-A stop: no-pool-fact; later tests not started'
  break
 fi
done
bun research/track-m/pack-section7-receipts.ts "$work"/*.log
