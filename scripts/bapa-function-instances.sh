#!/usr/bin/env bash
set -euo pipefail
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
bun install --frozen-lockfile > "$out/install.log" 2>&1
status=0
bun test research/bapa/function-instances.test.ts > "$out/tests.log" 2>&1 || status=$?
bunx --no-install tsc --noEmit --strict --skipLibCheck --target ES2022 --module ESNext --moduleResolution Bundler --allowImportingTsExtensions --types bun kernel/function-instances.ts research/bapa/function-instances.test.ts > "$out/typecheck.log" 2>&1 || status=$?
[ "$status" = 0 ] || exit "$status"
printf 'opt-in untrusted function-instance tests passed; no counted-use authority\n' > "$out/result.txt"
