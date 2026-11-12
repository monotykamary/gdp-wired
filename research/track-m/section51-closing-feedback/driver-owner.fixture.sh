#!/usr/bin/env bash
set -euo pipefail
kind=$1; mode=$2; out=$3; helper=$4
if [[ "$kind" == driver ]]; then
 printf '%s\n' "$$" > "$out/child-pid.txt"
 if [[ "$mode" == normal ]]; then sleep 0.1; exit 0; fi
 if [[ "$mode" == ignore ]]; then trap '' TERM; else trap 'printf terminated > "$out/child-term.txt"; exit 0' TERM; fi
 : > "$out/child-ready"
 while :; do sleep 0.05; done
fi
source "$helper"
driver_owner_init
scratch="$out/scratch"; mkdir "$scratch"
cleanup(){
 local code=$? terminal=false
 trap - EXIT; trap '' TERM INT HUP
 if driver_owner_retire; then terminal=true; fi
 driver_owner_receipt > "$out/retirement.json"
 if [[ "$terminal" == true ]]; then rm -rf -- "$scratch"; fi
 printf '{"workerExit":%s,"terminalBeforeRemoval":%s,"scratchRemoved":%s}\n' "$code" "$terminal" "$([[ ! -e "$scratch" ]] && echo true || echo false)" > "$out/cleanup.json"
 exit "$code"
}
trap cleanup EXIT
trap 'exit 143' TERM
trap 'exit 130' INT
bash "$helper" exec "$out/owner.identity" bash "$0" driver "$mode" "$out" "$helper" &
driver_owner_bind "$!" "$out/owner.identity"
if [[ "$mode" != normal ]]; then while [[ ! -e "$out/child-ready" ]]; do sleep 0.01; done; fi
: > "$out/worker-ready"
code=0; driver_owner_wait || code=$?
exit "$code"
