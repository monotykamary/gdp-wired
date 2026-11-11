#!/usr/bin/env bash
set -u
input=$1
mode=$2
out=$3
export PATH="$HOME/.local/bin:$PATH" SUPERCOMPUTER_CONTROLLER=1
source=$(tr -d '\n' < "$input/source.txt")
status=0
timeout 1920s supercomputer run --jobs "research/lane-i/strict-w-originals/$mode.jobs.json" --out "$out" --class gate --backend boat --data "$input:port-input" || status=$?
if [ -f "$out/placement.json" ]; then
 vm=$(jq -r --arg key "strict-originals-$mode" '.[$key].vm // empty' "$out/placement.json")
 if [ -n "$vm" ]; then
  mkdir -p "$out/artifacts"
  /home/user/.ascii/boat scp -r "$vm:/home/user/.sc-artifacts/lane-i-strict-originals/$source/$mode" "$out/artifacts" || status=1
 fi
fi
if [ -f "$out/summary.tsv" ]; then
 if ! awk '$2 != 0 {exit 1}' "$out/summary.tsv"; then status=1; fi
else status=1
fi
exit "$status"
