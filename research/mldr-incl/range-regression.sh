#!/usr/bin/env bash
# Frozen generated-family diagnostics only; helpers remain assumed.
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bash lane-e-preflight/apply.sh
for name in range-regression-input range-regression-input.test install-range-switch; do
 cp "range-tools/$name.txt" "research/mldr-incl/$name.ts"
done
bun test research/mldr-incl/range-regression-input.test.ts
if test "${1:-}" = check; then bun run check; exit; fi
mode=$1; shift
tmp=$(mktemp -d /tmp/incl-range.XXXXXX)
trap 'rm -rf "$tmp"' EXIT
bun research/mldr-incl/range-regression-input.ts range-input/fresh.log range-input/prior-family.json "$tmp/family.json"
bun research/mldr-incl/install-range-switch.ts
if test "$mode" = targeted; then bun research/mldr-incl/install-targeted-completion.ts; fi
failed=0
for spec in "$@"; do
 arm=${spec%:*}; units=${spec#*:}; skip=0
 if test "$arm" = off; then skip=1; fi
 dir="$tmp/$arm-$units"; mkdir "$dir"; cp "$tmp/family.json" "$dir/family-source.json"
 export MLDR_INCL_SKIP_INITIAL_RANGES=$skip MLDR_INCL_FAMILY=generated MLDR_INCL_VARIANT="range-$mode-$arm-$units" DUMP_DIR="$dir"
 code=0
 timeout -s KILL 45 bun research/mldr-incl/conditional-safety.ts "$tmp/family.json" "$units" no || code=$?
 if test -f "$dir/production-proof.json"; then bun research/mldr-incl/inspect-production.ts "$dir/production-proof.json" || code=$?; else echo NO_PRODUCTION_PROOF_TO_REPLAY; fi
 bun research/mldr-incl/pack-production.ts "$dir" || code=$?
 if test "$code" -ne 0; then failed=$code; fi
done
exit "$failed"
