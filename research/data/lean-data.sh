#!/bin/bash
# The Lean twin's library compiled (cached by modal/run.py), Data.lean with its errors shown, then the datatype items of
# lean-kernel/package-check.ts (ONLY=…), every error shown: `ONLY=datalen bash research/data/lean-data.sh`.
cd lean-kernel
export LEAN_PATH=$PWD:$(dirname $(dirname $(readlink -f $(elan which lean))))/lib/lean
for f in Cert Kernel Cyclic Progress StepLaw Steps Sets History Live Ghost Refine Bridge; do
  { [ -f $f.olean ] || lean -o $f.olean $f.lean; } > /dev/null 2>&1 || { echo build-failed $f; exit 1; }
done
[ -f Data.olean ] || lean -o Data.olean Data.lean 2>&1 | grep -v warning | head -60
[ -f Data.olean ] || { echo build-failed Data; exit 1; }
out=$(mktemp -d)
t0=$SECONDS
bun package-check.ts $out > /dev/null || exit 1
t1=$SECONDS
lean $out/Proofs.lean > $out/proofs.out 2>&1; s=$?
echo "export $((t1 - t0)) s, lean $((SECONDS - t1)) s"
for l in $(grep -o 'Proofs.lean:[0-9]*:[0-9]*: error' $out/proofs.out | cut -d: -f2 | head -8); do echo "--- line $l"; sed -n "$((l-2)),$((l+1))p" $out/Proofs.lean | cut -c1-200; done
grep -A10 'error' $out/proofs.out | head -120
grep 'depends on axioms' $out/proofs.out
for f in ${ONLY//,/ }; do awk "/^namespace $f/,/^end $f/" $out/Proofs.lean > /tmp/$f.lean; done
if grep -q "declaration uses 'sorry'" $out/proofs.out; then echo sorry; exit 1; fi
echo lean-exit $s; exit $s
