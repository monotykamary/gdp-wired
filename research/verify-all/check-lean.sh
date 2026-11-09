#!/usr/bin/env bash
set -eu
file=$1
root=$PWD
export LEAN_PATH="$root/lean-kernel"
lean --version
# Sources remain unchanged. Dependencies compile on boat; no native_decide, sorry, or external solver.
cd lean-kernel
for m in Cert Kernel Cyclic Progress StepLaw Steps Sets History Live Ghost GhostMap Sums Count CountMachine; do
  if [ ! -f "$m.olean" ] || [ "$m.lean" -nt "$m.olean" ]; then
    echo "LEAN_DEP $m"
    timeout -s KILL 600 lean -o "$m.olean" "$m.lean"
  fi
done
cd "$root"
sha256sum "$file"
/usr/bin/time -f 'LEAN_WALL seconds=%e maxrss_kb=%M exit=%x' timeout -s KILL 1200 lean "$file"
