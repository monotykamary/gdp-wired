#!/bin/bash
# Some items of lean-kernel/package-check.ts built against the twin's library compiled once and cached (supercomputer/run.py
# keeps lean-kernel/*.olean by a hash of their sources), not by `lake build`, which compiles the library again per job:
#   ONLY=a,b bash scripts/lean-items.sh    SHARD=1/4 bash scripts/lean-items.sh
# The lean-package-0 job builds the whole Lake project as a user would. Run from the repo root.
set -o pipefail
bun scripts/gen-lean-library.ts --check || exit 1
cd lean-kernel
export LEAN_PATH=$PWD:$(dirname $(dirname $(readlink -f $(elan which lean))))/lib/lean
for f in Cert Kernel Cyclic Progress StepLaw Steps Sets History Live NonTerm Ghost Sums Refine Bridge BridgeRules Data; do
  { [ -f $f.olean ] || lean -o $f.olean $f.lean; } > /dev/null 2>&1 || { echo build-failed $f; exit 1; }
done
t0=$SECONDS
out=$(mktemp -d)
bun package-check.ts $out || exit 1
t1=$SECONDS
lean $out/Proofs.lean > $out/proofs.out 2>&1; s=$?
echo "library $t0 s, export $((t1 - t0)) s, lean $((SECONDS - t1)) s"
grep -v 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' $out/proofs.out | tail -25
if grep -q -e "declaration uses 'sorry'" -e sorryAx $out/proofs.out; then echo sorry; exit 1; fi
echo lean-exit $s; exit $s
