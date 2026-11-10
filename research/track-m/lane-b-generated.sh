#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
out=$(mktemp -d "$HOME/track-m-lane-b-generated-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$out"' EXIT
timeout -s KILL 65 bun research/track-m/lane-b-family.ts "$out/family.json" --generated-only | tee "$out/generation.log"
