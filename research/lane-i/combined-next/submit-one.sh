#!/usr/bin/env bash
set -u
name=$1
mode=$2
input=$3
out=$4
limit=$5
export PATH="$HOME/.local/bin:$PATH" SUPERCOMPUTER_CONTROLLER=1
status=0
timeout "$limit" supercomputer run --jobs "research/lane-i/combined-next/$name.jobs.json" --out "$out" --class gate --backend boat --data "$input:port-input" || status=$?
if [ -f "$out/placement.json" ]; then
  vm=$(jq -r --arg name "$name" '.[$name].vm // empty' "$out/placement.json")
  tree=$(head -1 "$input/source.txt")
  if [ -n "$vm" ]; then
    mkdir -p "$out/artifacts"
    /home/user/.ascii/boat scp -r "$vm:/home/user/.sc-artifacts/lane-i-combined/$tree/$mode" "$out/artifacts" || status=1
    printf 'FETCHED_ARTIFACT_DIRECTORY %s/artifacts\n' "$out"
  fi
fi
if [ -f "$out/summary.tsv" ]; then
  job_exit=$(awk 'NR==1 {print $2; exit}' "$out/summary.tsv")
  if [ "$job_exit" != 0 ]; then status=1; fi
else
  status=1
fi
exit "$status"
