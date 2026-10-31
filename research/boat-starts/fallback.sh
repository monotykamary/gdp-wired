#!/bin/bash
# The fallback paths, each forced (research/boat-starts/fakeboat.py) on a small batch with --backend auto: what boat
# can't run must end on Modal, and finish (40 jobs of 20 s: not a tiny batch, which goes to Modal anyway). Each case's results in runs/laneP/fallback/<case>/ (summary.tsv's 4th column,
# backends.json's fallbacks); an empty registry (GDPW_LIVE) where warm VMs would hide the failure.
#   research/boat-starts/fallback.sh [nostarts api create lose image]
set -u
cd "$(dirname "$0")/../.."
out=runs/laneP/fallback; mkdir -p "$out"
jobs() { python3 -c "
import json,sys
n,s=int(sys.argv[1]),int(sys.argv[2])
j=[{'name':f'j{k}','cmd':f'echo job {k} on \$(hostname); sleep {s}','cpu':2.0,'timeout':300} for k in range(n)]
if len(sys.argv)>3: j+=[{'name':'own-image','cmd':'echo runner image; clang --version | head -1','image':'runner','timeout':300},{'name':'asks-modal','cmd':'echo asked for Modal','backend':'modal','timeout':300}]
print(json.dumps(j))" "$@"; }
export BOAT_BIN=$PWD/research/boat-starts/fakeboat.py
for c in ${@:-nostarts api create lose image}; do
  live=$(mktemp -d); jobs 40 20 $([ $c = lose ] && echo own) > "$out/$c.json"
  case $c in
    nostarts|api|create) env=(GDPW_FAKE_BOAT=$c GDPW_LIVE=$live) ;;
    lose) env=(GDPW_FAKE_BOAT=lose) ;;
    image) env=(GDPW_BOAT_IMAGE=gdpw-missing GDPW_LIVE=$live) ;;
  esac
  echo "=== $c (${env[*]})"
  env "${env[@]}" python3 supercomputer/run.py --backend auto --jobs "$out/$c.json" --out "$out/$c" --max-wait $([ $c = lose ] && echo 300 || echo 60) 2>&1 | grep -E "jobs, |fallback|boat can't|lost|refuses|on Modal" | tail -4
  rm -rf "$live"
done
