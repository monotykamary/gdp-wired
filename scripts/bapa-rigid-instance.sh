#!/usr/bin/env bash
set -euo pipefail
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
export PATH="$HOME/.bun/bin:$HOME/.local/bin:$PATH"
bun install --frozen-lockfile > "$out/install.log" 2>&1
status=0
bun test research/bapa/rigid-instance.test.ts research/bapa/rigid-lower.test.ts > "$out/tests.log" 2>&1 || status=$?
bunx --no-install tsc --noEmit --strict --skipLibCheck --target ES2022 --module ESNext --moduleResolution Bundler --allowImportingTsExtensions --types bun research/bapa/rigid-instance.ts research/bapa/rigid-instance.test.ts research/bapa/rigid-lower.ts research/bapa/rigid-lower.test.ts research/bapa/rigid-minimal.ts research/bapa/rigid-minimal-wrapper.ts research/bapa/export-rigid-minimal.ts > "$out/typecheck.log" 2>&1 || status=$?
[ "$status" = 0 ] || exit "$status"
printf 'isolated rigid-instance tests and typecheck passed; no kernel acceptance wiring\n' > "$out/result.txt"
