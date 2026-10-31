#!/bin/sh
# Stop what a dead client left running. First the Modal apps whose tickets are in this tree's own .live (a worktree's
# compare runners register there; a main checkout's .live is the supercomputer's shared directory): a ticket whose pid
# is gone marks an orphan; apps of live clients are only listed. With an app id, stop exactly that one. Then
# `supercomputer reap` (~/.local/share/supercomputer): every Modal app of a dead client in the shared directory, boat
# leases of dead clients released (what they ran killed) and VMs left up past their idle time stopped, RunPod pods
# whose client is gone deleted. Live clients' apps, VMs and pods are never touched.
cd "$(dirname "$0")"
if [ -n "$1" ]; then modal app stop -y "$1"; exit; fi
if [ -d .live ] && [ ! -L .live ]; then
  for t in .live/ap-*; do
    [ -e "$t" ] || continue
    id=$(basename "$t"); pid=$(cat "$t")
    if kill -0 "$pid" 2>/dev/null; then echo "live: $id (client $pid)"; else modal app stop -y "$id" >/dev/null 2>&1; rm -f "$t"; echo "stopped orphan $id"; fi
  done
fi
if command -v supercomputer >/dev/null 2>&1; then exec supercomputer --repo .. reap; fi
python3 boat.py reap
