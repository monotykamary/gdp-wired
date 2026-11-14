#!/usr/bin/env bash
set -euo pipefail
root=$PWD
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
mkdir -p "$out"
export PATH="$root/scripts/lean-gate:$PATH"
export LEAN_PATH="$root/lean-kernel:$(dirname "$(dirname "$(readlink -f "$(elan which lean)")")")/lib/lean"
cd lean-kernel
for m in Cert Kernel Count; do
  if [ ! -f "$m.olean" ]; then lean -o "$m.olean" "$m.lean" > "$out/$m.log" 2>&1; fi
done
lean -o Bounded.olean Bounded.lean > "$out/Bounded.log" 2>&1
cp Bounded.lean "$out/Bounded.lean"
lean BoundedMutants.lean > "$out/BoundedMutants.log" 2>&1
cd "$root"
bun scripts/bapa-mutants.ts
printf 'Bounded.lean and countermodels compiled through axiom gate; six false theorem mutants refused\n' | tee "$out/result.txt"
