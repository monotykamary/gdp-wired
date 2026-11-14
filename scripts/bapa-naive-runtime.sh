#!/usr/bin/env bash
set -euo pipefail
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
bun install --frozen-lockfile > "$out/install.log" 2>&1
status=0
bun test research/bapa/rigid-naive-runtime.test.ts research/bapa/rigid-instance.test.ts research/bapa/rigid-lower.test.ts > "$out/tests.log" 2>&1 || status=$?
bunx --no-install tsc --noEmit --strict --skipLibCheck --target ES2022 --module ESNext --moduleResolution Bundler --allowImportingTsExtensions --types bun research/bapa/rigid-naive-runtime.test.ts > "$out/typecheck.log" 2>&1 || status=$?
bunx --no-install oxlint --type-aware --deny-warnings --disable-nested-config research/bapa/rigid-naive-runtime.test.ts > "$out/lint.log" 2>&1 || status=$?
bunx @commitlint/cli --config research/egraph/historical/commitlint.config.cjs < BAPA-NAIVE-RUNTIME-COMMIT.txt > "$out/commitlint.log" 2>&1 || status=$?
printf '%s\n' "$status" > "$out/status.txt"
exit "$status"
