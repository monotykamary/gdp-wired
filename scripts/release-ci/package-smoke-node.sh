#!/usr/bin/env bash
# Invoked inside npm exec's Node-major-specific PATH; refuse accidental fallback.
set -euo pipefail
major=${1:?}; source=${2:?}
test "$(node -p 'process.versions.node.split(".")[0]')" = "$major"
cd "$source"
node --version
bun --version
bun install --frozen-lockfile
sh scripts/smoke.sh
