#!/usr/bin/env bash
# All controls and profiled runs are sequential in one exclusive VM/job.
set -euo pipefail
root="$PWD"
base=$(mktemp -d /tmp/track-m-phase-main-XXXXXX)
work=$(mktemp -d /tmp/track-m-phase-data-XXXXXX)
trap 'rm -rf "$base" "$work"' EXIT
(cd baseline-input && sha256sum -c main.tar.sha256)
revision=$(< baseline-input/revision.txt)
[[ "$revision" == 6a3874d3* ]] || { echo 'wrong main baseline'; exit 2; }
tar xf baseline-input/main.tar -C "$base"
mkdir -p "$base/research/track-m"
for file in phase-census-meter.ts run-phase-census.ts install-phase-census.ts; do cp "research/track-m/$file" "$base/research/track-m/$file"; done
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
(cd "$base" && bun install --frozen-lockfile >/dev/null)
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-phase-census.ts "$work/candidate-originals"
bun run check
bun test research/track-m/phase-census-meter.test.ts
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-phase-census.ts --restore "$work/candidate-originals"
(cd "$base" && TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-phase-census.ts "$work/main-originals")
(cd "$base" && TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-phase-census.ts --restore "$work/main-originals")
printf 'CENSUS baseline=%s candidate=50109a36 same-vm=true\n' "$revision"
TRACK_M_PHASE_CENSUS=0 timeout -s KILL 300 bun research/track-m/run-phase-census.ts focused replay-input/input.json candidate
TRACK_M_PHASE_CENSUS=0 timeout -s KILL 240 bun research/track-m/run-phase-census.ts native replay-input/input.json candidate
(cd "$base" && TRACK_M_PHASE_CENSUS=0 timeout -s KILL 240 bun research/track-m/run-phase-census.ts native "$root/replay-input/input.json" main)
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-phase-census.ts "$work/candidate-originals"
(cd "$base" && TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-phase-census.ts "$work/main-originals")
TRACK_M_PHASE_CENSUS=1 timeout -s KILL 300 bun research/track-m/run-phase-census.ts focused replay-input/input.json candidate
TRACK_M_PHASE_CENSUS=1 timeout -s KILL 240 bun research/track-m/run-phase-census.ts native replay-input/input.json candidate
(cd "$base" && TRACK_M_PHASE_CENSUS=1 timeout -s KILL 240 bun research/track-m/run-phase-census.ts native "$root/replay-input/input.json" main)
printf 'CENSUS all runs complete\n'
