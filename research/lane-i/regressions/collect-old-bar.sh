#!/usr/bin/env bash
# Read existing owned job receipts and kernel evidence only; never resume/stop a VM.
set -euo pipefail
out=${1:?}
while IFS=$'\t' read -r vm name; do
  if ! boat info "$vm" --json > "$out/$name.vm.json" 2> "$out/$name.vm.err"; then continue; fi
  state=$(jq -r '.sandbox.state // "missing"' "$out/$name.vm.json")
  if [[ "$state" != idle && "$state" != running ]]; then printf 'VM_UNAVAILABLE %s %s %s\n' "$vm" "$name" "$state"; continue; fi
  boat exec "$vm" --timeout 30 -- bash -lc '
    set +e
    p="$HOME/.sc/b/20261110-015931-92u7qg/jobs/'"$name"'"
    printf "JOB_DIRECTORY %s\n" "$p"
    if ! test -f "$p/done.json"; then printf "JOB_RECEIPT_MISSING\n"; exit 0; fi
    jq "{name,code,seconds,preempted,oom,error,launch_identity}" "$p/done.json"
    stat -c "DONE_TIME %Y %y" "$p/done.json"
    test ! -f "$p/pid" || awk "{print \"PARENT_PID \" \$1}" "$p/pid"
    end=$(stat -c %Y "$p/done.json")
    seconds=$(jq -r ".seconds|floor" "$p/done.json")
    begin=$((end-seconds-5)); end=$((end+5))
    printf "KERNEL_WINDOW %s %s\n" "$begin" "$end"
    sudo -n journalctl -k --no-pager -o short-iso --since "@$begin" --until "@$end" > /tmp/lane-i-old-kernel-'"$name"' 2>/tmp/lane-i-old-kernel-'"$name"'.err
    journal=$?
    printf "JOURNAL_EXIT %s\n" "$journal"
    grep -E "Out of memory|Killed process|oom-kill|Memory cgroup|memory pressure" /tmp/lane-i-old-kernel-'"$name"' | tail -n 160
    if test "$journal" != 0; then head -c 1000 /tmp/lane-i-old-kernel-'"$name"'.err; fi
    printf "CURRENT_VM_COUNTERS\n"
    awk "/^oom_kill /{print}" /proc/vmstat
    awk "/MemTotal|MemAvailable/{print}" /proc/meminfo
  ' > "$out/$name.exec.json" 2> "$out/$name.exec.err" || true
  printf 'COLLECTED %s %s\n' "$vm" "$name"
done < "$out/targets.tsv"
