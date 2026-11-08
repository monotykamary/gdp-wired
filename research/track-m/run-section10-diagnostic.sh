#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
work=$(mktemp -d /tmp/section10-diagnostic-XXXXXX)
out="$work/results"
mkdir -p "$out" "$work/A" "$work/B" "$work/leaf"
trap 'status=$?; shopt -s nullglob; files=("$out"/*); if ((${#files[@]})); then bun "$root/research/track-m/pack-section10-receipts.ts" "${files[@]}"; fi; rm -rf "$work"; exit "$status"' EXIT
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check > "$out/check.log" 2>&1
(cd baseline-input && sha256sum -c archive.sha256)
tar xzf baseline-input/baseline.tar.gz -C "$work/A"
for target in "$work/B" "$work/leaf"; do
 cp -a core kernel research package.json tsconfig.json "$target/"
done
for target in "$work/A" "$work/B" "$work/leaf"; do
 ln -s "$root/node_modules" "$target/node_modules"
 ln -s "$root/vendor" "$target/vendor"
 cp research/track-m/{section10-diagnostic.ts,install-section10-diagnostic.ts,run-section10-leaf-diagnostic.ts} "$target/research/track-m/"
done
for law in 'Inv*' Inv2973; do
 if [[ "$law" == 'Inv*' ]]; then file=star; else file=overlap; fi
 LAB_DEMAND_PROPOSALS=1 LAB_SOURCE_MS=5000 LAB_SOURCE_TRACE=1 LAB_CONDITIONAL_PROOF=1 timeout -s KILL 120 bun research/track-m/active-source-probe.ts "$root/replay-input/input.json" "$law" 5 all > "$out/$file-control.log" 2>&1
done
(cd "$work/leaf"; TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section10-diagnostic.ts leaf > "$out/leaf-install.json")
for law in 'Inv*' Inv2973; do
 if [[ "$law" == 'Inv*' ]]; then file=star; else file=overlap; fi
 (cd "$work/leaf"; DIAG_OUTPUT="$out/$file.json" LAB_DEMAND_PROPOSALS=1 LAB_SOURCE_MS=5000 LAB_SOURCE_TRACE=1 LAB_CONDITIONAL_PROOF=1 timeout -s KILL 180 bun research/track-m/run-section10-leaf-diagnostic.ts "$root/replay-input/input.json" "$law" 5 all > "$out/$file.log" 2>&1)
done
for side in A B; do
 (cd "$work/$side"; TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section10-diagnostic.ts cost > "$out/$side-install.json"; timeout -s KILL 120 bun research/track-m/profile-family.ts "$root/replay-input/input.json" > "$out/$side-cost.log" 2>&1)
done
