#!/usr/bin/env bash
set -euo pipefail
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
mkdir -p "$out"
phase=preflight
tests=-1
compiler=-1
tests_started=0
compiler_started=0
finish(){
 printf '{"schema":"k-lazy-suppliers-check/v1","source":"405b00adce54c7d7ed51139850ea5b0cbecde991","tree":"6f2e6351f09eea280a138a307a0823c1c3809b2f","phase":"%s","testsExit":%s,"compilerExit":%s,"testInvocations":%s,"compilerInvocations":%s,"profile":"GDP_WORK_FULL=1 GDP_ROWS_SHARED=1","compilerScope":"all seven changed production modules, unchanged generalized helper, three test files, transitive imports; strict project-equivalent flags","retries":0}\n' "$phase" "$tests" "$compiler" "$tests_started" "$compiler_started" > "$out/summary.json"
}
trap finish EXIT
cp scope-check-input/SOURCE.sha256 "$out/SOURCE.sha256"
cp scope-check-input/VENDORS.sha256 "$out/VENDORS.sha256"
sha256sum -c scope-check-input/SOURCE.sha256 > "$out/source-verification.log"
sha256sum -c scope-check-input/VENDORS.sha256 > "$out/vendor-verification.log"
phase=dependency-setup
tar -xf scope-check-input/gdp-ts.tar
tar -xf scope-check-input/handwired.tar
bun install --frozen-lockfile --ignore-scripts > "$out/install.log" 2>&1
cp node_modules/typescript/package.json "$out/typescript-package.json"
phase=tests
export GDP_WORK_FULL=1 GDP_ROWS_SHARED=1
tests_started=1
set +e
bun test --timeout 60000 core/count-scope-hyps.test.ts core/count-cert-transport-hard-stop.test.ts core/count-scope-lazy.test.ts > "$out/tests.log" 2>&1
tests=$?
set -e
printf 'K_LAZY_TESTS_EXIT=%s\n' "$tests"
phase=compiler
compiler_started=1
set +e
bun node_modules/typescript/bin/tsc --noEmit --allowImportingTsExtensions --moduleResolution bundler --target ES2022 --module ESNext --lib ESNext,DOM,DOM.Iterable --types bun,@webgpu/types --skipLibCheck --strict --noImplicitReturns --noFallthroughCasesInSwitch --noUncheckedIndexedAccess core/count-proof-scope.ts core/count-proof-rescope.ts core/count-scope-hyps.ts core/count-recipe-controller.ts core/counts.ts core/count-cert-transport.ts core/count-recovery/conditional-proof.ts core/work-admission.ts core/count-scope-hyps.test.ts core/count-cert-transport-hard-stop.test.ts core/count-scope-lazy.test.ts > "$out/compiler.log" 2>&1
compiler=$?
set -e
printf 'K_LAZY_COMPILER_EXIT=%s\n' "$compiler"
phase=complete
if [ "$tests" -eq 0 ] && [ "$compiler" -eq 0 ]; then exit 0; else exit 1; fi
