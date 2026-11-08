#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
work=$(mktemp -d /tmp/section10-calibration-XXXXXX)
out="$work/results"
mkdir -p "$out" "$work/control"
trap 'status=$?; shopt -s nullglob; files=("$out"/*); if ((${#files[@]})); then bun "$root/research/track-m/pack-section7-receipts.ts" "${files[@]}"; fi; rm -rf "$work"; exit "$status"' EXIT
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
(cd baseline-input && sha256sum -c archive.sha256)
tar xzf baseline-input/baseline.tar.gz -C "$work/control"
ln -s "$root/node_modules" "$work/control/node_modules"
ln -s "$root/vendor" "$work/control/vendor"
cp research/track-m/run-phase-census.ts research/track-m/phase-census-meter.ts "$work/control/research/track-m/"
printf 'baseline=' > "$out/environment.txt"
tr -d '\n' < baseline-input/baseline.commit >> "$out/environment.txt"
printf '\nboot_id=' >> "$out/environment.txt"
read -r boot_id < /proc/sys/kernel/random/boot_id
printf '%s\n' "$boot_id" >> "$out/environment.txt"
bun --version >> "$out/environment.txt"
(cd "$work/control" && TRACK_M_PHASE_CENSUS=0 timeout -s KILL 300 bun research/track-m/run-phase-census.ts focused "$root/replay-input/input.json" fresh-control > "$out/census-control.log" 2> "$out/census-control.stderr.log")
