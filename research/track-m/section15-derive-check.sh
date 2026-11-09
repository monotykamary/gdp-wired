#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
LAB_DISPOSABLE=1 bun research/track-m/section15-leaf-variant.ts after
LAB_DISPOSABLE=1 bun research/track-m/section15-derive-variant.ts after
bun run check
bun test research/track-m/section15-derive-order.test.ts core/count-recovery/{derivability-closure,conditional-proof,conditional-check-cache,field-demand,leaf-allowance,row-cases}.test.ts
