#!/usr/bin/env bash
set -euo pipefail
control=${1:?guarded-domain or tight-domain}
proof=$(mktemp /tmp/incl-pointwise.XXXXXX)
trap 'rm -f "$proof"' EXIT
MLDR_POINTWISE_OUT="$proof" timeout -s KILL 30 bun research/mldr-incl/pointwise.ts 'research/mldr-incl/fixtures/e14-safety.br#stage-0.json' S 'inX$canVote$3' "$control" 1000
test -s "$proof"
bun research/mldr-incl/verify-pointwise.ts "$proof"
