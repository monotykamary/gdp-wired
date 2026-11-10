#!/usr/bin/env bash
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
LAB_DISPOSABLE=1 bun research/track-m/section15-leaf-variant.ts after
bun run check
bun test research/track-m/section15-leaf-count.test.ts core/count-completion.test.ts core/count-recovery/{field-demand,field-bound-lemmas,guard-cases,field-bound-budget,leaf-allowance,member-inclusions,row-cases}.test.ts
