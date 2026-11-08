#!/usr/bin/env bash
# Isolate the unchanged 60s co-write test on both pre-review and fixed kernel sources.
set -euo pipefail
work=$(mktemp -d /tmp/track-k-co-write.XXXXXX)
trap 'rm -rf "$work"' EXIT
cp -a . "$work/tree"
cd "$work/tree"
cp kernel/kernel.ts "$work/fixed.ts"
bun install --frozen-lockfile >/dev/null
cp research/track-k/review-source/kernel-before-fixes.ts.txt kernel/kernel.ts
echo 'CONTROL begin pre-review'
set +e
bun test core/exists-support.test.ts -t 'co-write provenance closes a renamed forwarding pipeline with nothing written'
base=$?
set -e
echo "CONTROL end pre-review exit=$base"
cp "$work/fixed.ts" kernel/kernel.ts
echo 'CONTROL begin fixed'
set +e
bun test core/exists-support.test.ts -t 'co-write provenance closes a renamed forwarding pipeline with nothing written'
fixed=$?
set -e
echo "CONTROL end fixed exit=$fixed"
test "$base" -eq 0 && test "$fixed" -eq 0
