#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
if [[ ! -d node_modules/typescript ]]; then bun install --frozen-lockfile >/dev/null; fi
out=$(mktemp -d "$HOME/track-m-section14-law-root-XXXXXX")
timeout -s KILL 540 bun research/track-m/section14-law-root.ts runtime/overlap.packet.json seeds/root-seeds.json "$out" > "$out/probe.log" 2>&1
bun research/track-m/pack-section10-archive.ts "$out"/*
