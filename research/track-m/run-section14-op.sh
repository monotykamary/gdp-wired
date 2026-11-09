#!/usr/bin/env bash
set -euo pipefail
op="$1"; allowance="${2:-50000}"; mode="${3:-seeded}"
seed=(); if [[ "$mode" == seeded ]]; then seed=(seeds/root-seeds.json); fi
out=$(mktemp -d "$HOME/track-m-section14-op-XXXXXX")
(cd ready && sha256sum -c runtime.sha256)
timeout -s KILL 600 bun ready/replay.js runtime/overlap.packet.json "$op" "$out" "$allowance" "${seed[@]}" > "$out/replay.log" 2>&1
bun research/track-m/pack-section10-archive.ts "$out"/*
