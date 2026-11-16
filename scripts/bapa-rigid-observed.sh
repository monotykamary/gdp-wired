#!/usr/bin/env bash
set -euo pipefail
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
bun install --frozen-lockfile > "$out/install.log" 2>&1
# Parent writes progress.jsonl every ten seconds even when proof thread is busy.
# The returned report may be unknown/budget; exit 2 is not an infrastructure error.
bun research/bapa/observed-proof.ts > "$out/proof.log" 2>&1
