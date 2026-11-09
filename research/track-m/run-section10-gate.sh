#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
work=$(mktemp -d /tmp/section10-gate-XXXXXX)
out="$work/results"
mkdir -p "$out" "$work/baseline"
trap 'status=$?; shopt -s nullglob; files=("$out"/*); if ((${#files[@]})); then bun "$root/research/track-m/pack-section10-receipts.ts" "${files[@]}"; fi; rm -rf "$work"; exit "$status"' EXIT
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check > "$out/check.log" 2>&1
bun test core/count-recovery core/count-focused.test.ts core/count-demand.test.ts core/count-cases.test.ts core/count-focus-proof.test.ts core/count-write-frames.test.ts core/count-cert-transport.test.ts > "$out/tests.log" 2>&1
(cd baseline-input && sha256sum -c archive.sha256)
tar xzf baseline-input/baseline.tar.gz -C "$work/baseline"
ln -s "$root/node_modules" "$work/baseline/node_modules"
ln -s "$root/vendor" "$work/baseline/vendor"
cp research/track-m/profile-cost-wins.ts "$work/baseline/research/track-m/profile-cost-wins.ts"
bun research/track-m/run-section10-gate.ts "$root" "$work/baseline" "$root/replay-input/input.json" "$out"
