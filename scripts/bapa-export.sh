#!/usr/bin/env bash
set -euo pipefail
root=$PWD
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
export PATH="$root/scripts/lean-gate:$PATH"
export LEAN_PATH="$root/lean-kernel:$(dirname "$(dirname "$(readlink -f "$(elan which lean)")")")/lib/lean"
bun install --frozen-lockfile > "$out/install.log" 2>&1
bun lean-kernel/bounded-examples.ts > "$out/export.log" 2>&1
cd lean-kernel
for m in Cert Kernel Cyclic Progress StepLaw Steps Sets History Live NonTerm Ghost Sums Refine Bridge BridgeRules Data Count CountMachine GhostMap QAlpha; do
  if [ ! -f "$m.olean" ]; then lean -o "$m.olean" "$m.lean" > "$out/$m.log" 2>&1; fi
done
lean "$out/BoundedExamples.lean" > "$out/BoundedExamples.log" 2>&1
printf 'Three marked machines and six automatically derived region identities checked by the unchanged Lean twin\n' > "$out/result.txt"
