#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
work=$(mktemp -d /tmp/section10-deep-diagnostic-XXXXXX)
out="$work/results"
mkdir -p "$out" "$work/A" "$work/B" "$work/full"
trap 'status=$?; shopt -s nullglob; files=("$out"/*); if ((${#files[@]})); then bun "$root/research/track-m/pack-section10-receipts.ts" "${files[@]}"; fi; rm -rf "$work"; exit "$status"' EXIT
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check > "$out/check.log" 2>&1
bun test research/track-m/section10-diagnostic.test.ts > "$out/tests.log" 2>&1
(cd baseline-input && sha256sum -c archive.sha256)
tar xzf baseline-input/baseline.tar.gz -C "$work/A"
for target in "$work/B" "$work/full"; do cp -a core kernel research package.json tsconfig.json "$target/"; done
for target in "$work/A" "$work/B" "$work/full"; do
 ln -s "$root/node_modules" "$target/node_modules"
 ln -s "$root/vendor" "$target/vendor"
 cp research/track-m/{section10-diagnostic.ts,install-section10-diagnostic.ts} "$target/research/track-m/"
done
(cd "$work/full"; TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section10-diagnostic.ts family > "$out/full-install.json"; timeout -s KILL 180 bun research/track-m/profile-family.ts "$root/replay-input/input.json" > "$out/full.log" 2>&1)
for side in A B; do
 (cd "$work/$side"; TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section10-diagnostic.ts cost > "$out/$side-install.json"; timeout -s KILL 120 bun research/track-m/profile-family.ts "$root/replay-input/input.json" > "$out/$side-cost.log" 2>&1)
done
