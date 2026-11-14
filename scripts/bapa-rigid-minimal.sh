#!/usr/bin/env bash
set -euo pipefail
root=$PWD
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
export PATH="$HOME/.bun/bin:$root/scripts/lean-gate:$PATH"
export LEAN_PATH="$root/lean-kernel:$(dirname "$(dirname "$(readlink -f "$(elan which lean)")")")/lib/lean"
bun install --frozen-lockfile > "$out/install.log" 2>&1
bun research/bapa/export-rigid-minimal.ts > "$out/export.log" 2>&1
cd lean-kernel
for m in Cert Kernel Cyclic Progress StepLaw Steps Sets History Live NonTerm Ghost Sums Refine Bridge BridgeRules Data Count CountMachine GhostMap QAlpha Rigid RigidEncoding; do
  if [ ! -f "$m.olean" ]; then lean -o "$m.olean" "$m.lean" > "$out/$m.log" 2>&1; fi
done
lean "$out/RigidMinimalGenerated.lean" > "$out/RigidMinimalGenerated.log" 2>&1
printf 'GIVEN-seed diagnostic certificate and original-source wrapper checked; automatic instantiation gate still pending\n' > "$out/result.txt"
