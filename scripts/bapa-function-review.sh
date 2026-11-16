#!/usr/bin/env bash
set -euo pipefail
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
bun install --frozen-lockfile > "$out/install.log" 2>&1
status=0
bun test research/bapa/function-instances.test.ts > "$out/tests.log" 2>&1 || status=$?
bunx --no-install tsc --noEmit --strict --skipLibCheck --target ES2022 --module ESNext --moduleResolution Bundler --allowImportingTsExtensions --types bun kernel/function-instances.ts research/bapa/function-instances.test.ts research/bapa/rigid-naive.ts research/bapa/prove-rigid-naive.ts research/bapa/export-rigid-auto.ts > "$out/typecheck.log" 2>&1 || status=$?
bunx --no-install oxlint --type-aware --deny-warnings --disable-nested-config kernel/function-instances.ts kernel/prove.ts research/bapa/rigid-instance.ts research/bapa/rigid-lower.ts research/bapa/rigid-minimal.ts research/bapa/rigid-minimal-wrapper.ts research/bapa/export-rigid-minimal.ts research/bapa/export-rigid-auto.ts research/bapa/function-instances.test.ts research/bapa/rigid-naive.ts research/bapa/prove-rigid-naive.ts > "$out/lint.log" 2>&1 || status=$?
bunx @commitlint/cli --config research/egraph/historical/commitlint.config.cjs < BAPA-SLICE3-COMMIT.txt > "$out/commitlint.log" 2>&1 || status=$?
[ "$status" = 0 ] || exit "$status"
printf 'changed-path tests, strict TypeScript, type-aware lint and commitlint passed\n' > "$out/result.txt"
