#!/usr/bin/env bash
# Frozen-family conditional probe. Never changes production or installs a law.
set -euo pipefail
rank=${1:?rank or control required}
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bash lane-e-preflight/apply.sh
for name in range-regression-input range-regression-input.test install-range-switch; do
 cp "range-tools/$name.txt" "research/mldr-incl/$name.ts"
done
for name in install-member-source-rank install-member-source-rank.test; do
 cp "rank-tools/$name.txt" "research/mldr-incl/$name.ts"
done
bun research/mldr-incl/install-range-switch.ts
if test "$rank" != control; then bun research/mldr-incl/install-member-source-rank.ts "$rank"; fi
bun run check
bun test research/mldr-incl/install-member-source-rank.test.ts research/mldr-incl/range-regression-input.test.ts
tmp=$(mktemp -d /tmp/incl-rank.XXXXXX)
trap 'rm -rf "$tmp"' EXIT
bun research/mldr-incl/range-regression-input.ts range-input/fresh.log range-input/prior-family.json "$tmp/family.json"
failed=0
for units in 2700 6000; do
 dir="$tmp/$units"; mkdir "$dir"; cp "$tmp/family.json" "$dir/family-source.json"
 export MLDR_INCL_SKIP_INITIAL_RANGES=1 MLDR_INCL_FAMILY=generated MLDR_INCL_VARIANT="member-rank-$rank-$units" DUMP_DIR="$dir"
 code=0
 timeout -s KILL 45 bun research/mldr-incl/conditional-safety.ts "$tmp/family.json" "$units" no || code=$?
 if test -f "$dir/production-proof.json"; then bun research/mldr-incl/inspect-production.ts "$dir/production-proof.json" || code=$?; else echo NO_PRODUCTION_PROOF_TO_REPLAY; fi
 bun research/mldr-incl/pack-production.ts "$dir" || code=$?
 if test "$code" -ne 0; then failed=$code; fi
done
exit "$failed"
