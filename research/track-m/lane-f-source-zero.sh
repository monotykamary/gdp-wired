#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
sha256sum -c SHA256SUMS
work=$(mktemp -d "$HOME/lane-f-source-zero-XXXXXX")
trap 'bash research/track-m/pack-section18-archive.sh "$work"' EXIT
mkdir -p "$work/capture" "$work/packets"
tar xzf archives/overlap.tar.gz -C "$work/capture"
bun research/track-m/lane-f-freeze.ts "$work/capture" overlap "$work/packets"
bun research/track-m/lane-f-source-zero.ts "$work/packets/overlap.packet.json" "$work/result"
