#!/usr/bin/env bash
# Worker only. Keep the repaired release snapshot separate from the frozen supplement.
set -euo pipefail
control=$PWD
major=${1:?usage: package-smoke.sh NODE_MAJOR}
case "$major" in 20|24) ;; *) echo 'only Node 20 and 24 are release smoke targets' >&2; exit 2;; esac
d=$(mktemp -d /tmp/gdp-release-package.XXXXXX)
trap 'rm -rf "$d"' EXIT
bash "$control/setup-b11.sh" "$control/release-meta" "$d/tree"
cd "$d/tree"
# npm's node package puts that major first on PATH for the entire child smoke, including npx.
npm exec --yes --package="node@$major" -- bash "$control/package-smoke-node.sh" "$major" "$PWD"
printf 'PACKAGE_SMOKE_SOURCE '; git rev-parse HEAD
printf 'PACKAGE_SMOKE_NODE_MAJOR %s\n' "$major"
