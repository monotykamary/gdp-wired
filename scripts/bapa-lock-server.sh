#!/usr/bin/env bash
set -euo pipefail
root=$PWD
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
export PATH="$root/scripts/lean-gate:$PATH"
export LEAN_PATH="$root/lean-kernel:$(dirname "$(dirname "$(readlink -f "$(elan which lean)")")")/lib/lean"
bun install --frozen-lockfile > "$out/install.log" 2>&1
bun test research/bapa/lock-server-sized.test.ts > "$out/tests.log" 2>&1
bun research/bapa/export-lock-server.ts > "$out/export.log" 2>&1
cd lean-kernel
for m in Cert Kernel Cyclic Progress StepLaw Steps Sets History Live NonTerm Ghost Sums Refine Bridge BridgeRules Data Count CountMachine GhostMap QAlpha; do
  if [ ! -f "$m.olean" ]; then lean -o "$m.olean" "$m.lean" > "$out/$m.log" 2>&1; fi
done
lean "$out/LockServerSized.lean" > "$out/LockServerSized.log" 2>&1
printf 'Symbolic uncounted lock-server proof (helper given, not found) and runtime correspondence checked\n' > "$out/result.txt"
