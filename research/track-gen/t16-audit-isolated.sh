#!/usr/bin/env bash
# Focused audit validation of an immutable commit, not a full merge gate.
set -euo pipefail
root=$PWD
archive="$root/audit/audit.tar"
test "$(git get-tar-commit-id < "$archive")" = "$SOURCE_COMMIT"
printf 'AUDIT_COMMIT=%s\n' "$SOURCE_COMMIT"
sha256sum "$archive"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
tar -xf "$archive" -C "$scratch"
mkdir -p "$scratch/vendor"
cp -R "$root/vendor/." "$scratch/vendor/"
cd "$scratch"
bun install --frozen-lockfile
bun test core/count-cubes.test.ts core/counts-preflight.test.ts core/small-counts.test.ts
bun research/track-gen/t16-audit-probe.ts
bun run check
for message in T16-AUDIT-COMMIT.txt T16-AUDIT-CYCLE-COMMIT.txt T16-AUDIT-REPORT-COMMIT.txt; do
  bunx --yes @commitlint/cli --config research/egraph/historical/commitlint.config.cjs < "research/track-gen/$message"
done
