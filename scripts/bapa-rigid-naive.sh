#!/usr/bin/env bash
set -euo pipefail
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
bun install --frozen-lockfile > "$out/install.log" 2>&1
bun research/bapa/prove-rigid-naive.ts > "$out/proof.log" 2>&1
printf 'unseeded original-quorum machine proved with GIVEN source helpers; not a counted run or final source export\n' > "$out/result.txt"
