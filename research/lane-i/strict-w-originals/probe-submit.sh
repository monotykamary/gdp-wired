#!/usr/bin/env bash
set -u
input=$1
out=$2
export PATH="$HOME/.local/bin:$PATH" SUPERCOMPUTER_CONTROLLER=1
status=0
timeout 1320s supercomputer run --jobs research/lane-i/strict-w-originals/probe.jobs.json --out "$out" --class gate --backend boat --data "$input:port-input" || status=$?
if [ -f "$out/placement.json" ]; then
 vm=$(jq -r '.["original-first-crossings"].vm // empty' "$out/placement.json")
 if [ -n "$vm" ]; then
  mkdir -p "$out/artifacts"
  $HOME/.ascii/boat scp -r "$vm:~/.sc-artifacts/lane-i-strict-originals/6115f86a8eade60c58aadf86df525548c04be6b9/first-crossings" "$out/artifacts" || status=1
 fi
fi
if [ -f "$out/summary.tsv" ]; then
 if ! awk '$2 != 0 {exit 1}' "$out/summary.tsv"; then status=1; fi
else status=1
fi
exit "$status"
