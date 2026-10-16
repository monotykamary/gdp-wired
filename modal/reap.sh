#!/bin/sh
# Stop Modal apps whose local client died: modal/run.py writes modal/.live/<app id> holding its client pid and removes
# it when done, so a ticket whose pid is gone marks an orphan. Apps of live clients, and apps this runner didn't start,
# are listed but never stopped. With an app id, stop exactly that one.
cd "$(dirname "$0")"
if [ -n "$1" ]; then modal app stop -y "$1"; exit; fi
mkdir -p .live
for t in .live/ap-*; do
  [ -e "$t" ] || continue
  id=$(basename "$t"); pid=$(cat "$t")
  if kill -0 "$pid" 2>/dev/null; then echo "live: $id (client $pid)"; else modal app stop -y "$id" >/dev/null 2>&1; rm -f "$t"; echo "stopped orphan $id"; fi
done
modal app list --json 2>/dev/null | python3 -c '
import json, sys
up = [a for a in json.load(sys.stdin) if a["state"] not in ("stopped", "stopping...")]
print(len(up), "apps up")
for a in up: print(" ", a["app_id"], a["description"], a["state"], "tasks=" + str(a["tasks"]))'
