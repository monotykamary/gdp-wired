#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
LAB_DISPOSABLE=1 bun research/track-m/section15-leaf-variant.ts after
LAB_DISPOSABLE=1 bun research/track-m/section15-derive-variant.ts after
LAB_DISPOSABLE=1 bun research/track-m/section15-row-variant.ts after
bun run check
bun test research/track-m/section15-row-probe.test.ts core/count-recovery/{row-cases,derivability-closure,conditional-proof}.test.ts
