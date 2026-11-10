#!/usr/bin/env bash
# Source-checked generated family, independent replay at each fixed allowance.
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check
bun test research/mldr-incl/pack-production.test.ts
tmp=$(mktemp -d /tmp/incl-budgets.XXXXXX)
trap 'rm -rf "$tmp"' EXIT
GENERATOR_REV=${GENERATOR_REV:?source revision required} MLDR_INCL_FAMILY_OUT="$tmp/family-source.json" bun research/mldr-incl/capture-generation.ts mldr
failed=0
for units in 2700 6000; do
 dir="$tmp/$units"; mkdir "$dir"; cp "$tmp/family-source.json" "$dir/family-source.json"
 code=0
 MLDR_INCL_VARIANT="flags-first-$units" MLDR_INCL_FAMILY=generated DUMP_DIR="$dir" timeout -s KILL 45 bun research/mldr-incl/conditional-safety.ts "$dir/family-source.json" "$units" no || code=$?
 if test -f "$dir/production-proof.json"; then
  bun research/mldr-incl/inspect-production.ts "$dir/production-proof.json" || code=$?
 else
  echo NO_PRODUCTION_PROOF_TO_REPLAY
 fi
 bun research/mldr-incl/pack-production.ts "$dir" || code=$?
 if test "$code" -ne 0; then failed=$code; fi
done
exit "$failed"
