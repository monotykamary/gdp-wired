#!/usr/bin/env bash
set -eu
id=$1; mode=$2
bun install --frozen-lockfile >/dev/null
mkdir -p /tmp/verify-capture
file=/tmp/verify-capture/$id-$mode
cpus=$(python3 -c 'import os; print(",".join(map(str,sorted(os.sched_getaffinity(0))[:4])))')
echo "CAPTURE id=$id mode=$mode cpus=$cpus"
sha256sum core/dsl.ts kernel/prove.ts kernel/kernel.ts research/verify-all/capture.ts research/verify-all/export-captured.ts
skip=broken
if [ "$mode" = broken ]; then skip=search; fi
set +e
VERIFY_CAPTURE=$file.json /usr/bin/time -f 'CAPTURE_WALL seconds=%e exit=%x' taskset -c "$cpus" timeout -s KILL 60 bun --preload ./research/verify-all/capture.ts research/protocols/ic3syn/run.ts --ms 60000 --only "$id" --skip "$skip"
s=$?
echo "CAPTURE_EXIT $s"
if [ -f "$file.json" ]; then
  timeout -s KILL 180 bun research/verify-all/export-captured.ts "$file.json" "$file.lean"
  e=$?
  echo "EXPORT_EXIT $e"
  if [ -f "$file.lean" ]; then
    bash research/verify-all/check-lean.sh "$file.lean"
    echo "LEAN_EXIT $?"
  fi
  sha256sum "$file".*
  # Persist small compressed packets in the evidence log, bounded beneath the runner's 400 KB cap.
  tar -cJf "$file.tar.xz" -C /tmp/verify-capture $(basename "$file.json") $(test -f "$file.result.json" && basename "$file.result.json") $(test -f "$file.lean" && basename "$file.lean")
  size=$(wc -c < "$file.tar.xz")
  sha256sum "$file.tar.xz"
  echo "ARCHIVE_BYTES $size"
  if [ "$size" -le 220000 ]; then echo 'ARCHIVE_BEGIN'; base64 -w0 "$file.tar.xz"; echo; echo 'ARCHIVE_END'; else echo 'ARCHIVE_TOO_LARGE retained on boat only'; fi
fi
exit 0
