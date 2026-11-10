#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
out=$(mktemp -d /tmp/section10-implementation-XXXXXX)
trap 'status=$?; shopt -s nullglob; files=("$out"/*); if ((${#files[@]})); then bun "$root/research/track-m/pack-section10-receipts.ts" "${files[@]}"; fi; rm -rf "$out"; exit "$status"' EXIT
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check > "$out/check.log" 2>&1
bun test core/count-recovery core/count-focused.test.ts core/count-demand.test.ts core/count-cases.test.ts core/count-focus-proof.test.ts core/count-write-frames.test.ts core/count-cert-transport.test.ts > "$out/tests.log" 2>&1
bun research/track-m/probe-section10-generator.ts replay-input/input.json > "$out/generator.log" 2>&1
for law in 'Inv*' Inv2973; do
 if [[ "$law" == 'Inv*' ]]; then file=loop-star.log; else file=loop-overlap.log; fi
 LAB_DEMAND_PROPOSALS=1 LAB_SOURCE_MS=5000 LAB_SOURCE_TRACE=1 LAB_CONDITIONAL_PROOF=1 timeout -s KILL 90 bun research/track-m/active-source-probe.ts replay-input/input.json "$law" 5 all > "$out/$file" 2> "$out/$file.stderr"
done
