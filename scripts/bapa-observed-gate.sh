#!/usr/bin/env bash
set -euo pipefail
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
bun install --frozen-lockfile > "$out/install.log" 2>&1
status=0
bun test research/bapa/function-instances.test.ts research/bapa/observed-proof.test.ts > "$out/tests.log" 2>&1 || status=$?
bunx --no-install tsc --noEmit --strict --skipLibCheck --target ES2022 --module ESNext --moduleResolution Bundler --allowImportingTsExtensions --types bun research/bapa/observed-proof.ts research/bapa/observed-proof-worker.ts research/bapa/observed-proof.test.ts kernel/function-instances.ts > "$out/typecheck.log" 2>&1 || status=$?
bunx --no-install oxlint --type-aware --deny-warnings --disable-nested-config research/bapa/observed-proof.ts research/bapa/observed-proof-worker.ts research/bapa/observed-proof.test.ts kernel/function-instances.ts > "$out/lint.log" 2>&1 || status=$?
for message in BAPA-PROGRESS-COMMIT.txt BAPA-TIMEOUT-COMMIT.txt; do bunx @commitlint/cli --config research/egraph/historical/commitlint.config.cjs < "$message" >> "$out/commitlint.log" 2>&1 || status=$?; done
[ "$status" = 0 ] || exit "$status"
mkdir -p "$out/actual-worker-smoke"
SUPERCOMPUTER_OUTPUT_DIR="$out/actual-worker-smoke" BAPA_OBSERVED_MODEL=minimal bash scripts/bapa-rigid-observed.sh > "$out/actual-worker-smoke.log" 2>&1
printf 'progress worker, own-work/wall budget controls, strategy tests, strict TS, lint and commitlint passed\n' > "$out/result.txt"
