#!/usr/bin/env bash
# Worker only: prepared metadata for the frozen supplement, never the release-prep tip.
set -euo pipefail
control=$PWD
d=$(mktemp -d /tmp/gdp-c841-verify.XXXXXX)
trap 'rm -rf "$d"' EXIT
bash "$control/setup-b11.sh" "$control/candidate-meta" "$d/tree"
cd "$d/tree"
bun install --frozen-lockfile
expected=$(<"$control/candidate-meta/main.sha")
bun "$control/e0-verify.ts" "$PWD" "$control/current-receipts" "$d/decoded" "$expected"
bun "$control/verify-negative-controls.ts" "$control/e0-verify.ts" "$PWD" "$control/current-receipts" "$d" "$expected"
