#!/usr/bin/env bash
set -euo pipefail
out=$(mktemp -d "$HOME/track-m-section14-roots-XXXXXX")
(cd ready && sha256sum -c runtime.sha256)
timeout -s KILL 540 bun ready/roots.js runtime/overlap.packet.json candidates/indices.json "$out" 1000 > "$out/roots.log" 2>&1
bun research/track-m/pack-section10-archive.ts "$out"/*
