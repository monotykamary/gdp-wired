#!/usr/bin/env bash
set -euo pipefail
source research/kernel-sums/pin-node.sh
trap 'rm -f core/public-focused-probe.mjs; if [[ -n ${node_cache:-} ]]; then rm -rf "$node_cache"; fi' EXIT
export LEAN_PATH="$PWD/lean-kernel"
cp research/kernel-sums/focused.mjs core/public-focused-probe.mjs
"$NODE" --experimental-transform-types --disable-warning=ExperimentalWarning core/public-focused-probe.mjs "$1" "$2" "$SUPERCOMPUTER_OUTPUT_DIR/exact.lean" | tee "$SUPERCOMPUTER_OUTPUT_DIR/native.txt"
for module in Cert Kernel Progress StepLaw Steps Sets History Live Ghost Count Sums GhostMap FiniteSumComposition GhostSourceViews GhostWriteTransport; do
  if [[ ! -f lean-kernel/$module.olean ]]; then lean -o lean-kernel/$module.olean lean-kernel/$module.lean; fi
done
lean "$SUPERCOMPUTER_OUTPUT_DIR/exact.lean" | tee "$SUPERCOMPUTER_OUTPUT_DIR/lean.txt"
python3 - "$SUPERCOMPUTER_OUTPUT_DIR/lean.txt" <<'PY'
import re, sys
text = open(sys.argv[1]).read()
a = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text)
assert any(k == 'Replay.original_law' for k, _ in a), a
assert all({x.strip() for x in axes.split(',')} <= {'propext', 'choice', 'Classical.choice', 'Quot.sound'} for _, axes in a), a
PY
