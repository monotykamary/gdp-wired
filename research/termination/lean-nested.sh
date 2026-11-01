#!/bin/bash
# research/termination/Nested.lean in Lean: the library compiled (Data.lean's wf_fix_inv_unique among it), the example
# checked, every error shown, the axioms each theorem depends on.
cd "$(dirname "$0")/../../lean-kernel"
export LEAN_PATH=$PWD:$(dirname $(dirname $(readlink -f $(elan which lean))))/lib/lean
for f in Cert Kernel Cyclic Progress StepLaw Steps Sets History Live Ghost Refine Bridge BridgeRules Data; do
  { [ -f $f.olean ] && [ $f != Data ] || lean -o $f.olean $f.lean; } > /tmp/lean-$f.out 2>&1 || { echo build-failed $f; cat /tmp/lean-$f.out; exit 1; }
done
lean ../research/termination/Nested.lean > /tmp/nested.out 2>&1; s=$?
cat /tmp/nested.out
if grep -q "declaration uses 'sorry'" /tmp/nested.out; then echo sorry; exit 1; fi
echo lean-exit $s; exit $s
