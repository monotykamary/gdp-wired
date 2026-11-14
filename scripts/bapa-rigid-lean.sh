#!/usr/bin/env bash
set -euo pipefail
root=$PWD
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
export PATH="$root/scripts/lean-gate:$PATH"
export LEAN_PATH="$root/lean-kernel:$(dirname "$(dirname "$(readlink -f "$(elan which lean)")")")/lib/lean"
cd lean-kernel
for m in Cert Kernel Cyclic Progress StepLaw Steps Sets; do
  if [ ! -f "$m.olean" ]; then lean -o "$m.olean" "$m.lean" > "$out/$m.log" 2>&1; fi
done
lean -o Rigid.olean Rigid.lean > "$out/Rigid.log" 2>&1
lean RigidNaive.lean > "$out/RigidNaive.log" 2>&1
lean RigidMutants.lean > "$out/RigidMutants.log" 2>&1
printf 'Rigid source-axiom bridge checked\n' > "$out/result.txt"
