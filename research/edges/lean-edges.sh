#!/bin/bash
# examples/abstract.ts's laws in Lean, as research/data/lean-data.sh checks the datatype items: the library compiled, the
# export, `lean Proofs.lean`, every error shown, the axioms each theorem depends on.
cd lean-kernel
export LEAN_PATH=$PWD:$(dirname $(dirname $(readlink -f $(elan which lean))))/lib/lean
for f in Cert Kernel Cyclic Progress StepLaw Steps Sets History Live Ghost Refine Bridge BridgeRules Data; do
  { [ -f $f.olean ] || lean -o $f.olean $f.lean; } > /dev/null 2>&1 || { echo build-failed $f; exit 1; }
done
out=$(mktemp -d)
bun ../research/edges/lean-edges.ts $out || exit 1
lean $out/Proofs.lean > $out/proofs.out 2>&1; s=$?
grep -A10 'error' $out/proofs.out | head -120
grep 'depends on axioms' $out/proofs.out
grep -c '^theorem' $out/Proofs.lean
if grep -q "declaration uses 'sorry'" $out/proofs.out; then echo sorry; exit 1; fi
echo lean-exit $s; exit $s
