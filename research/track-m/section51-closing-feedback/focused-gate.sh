#!/usr/bin/env bash
# One B-only focused gate, after K's accepted gate. Never run the MLDR model.
set -euo pipefail
export PATH="$HOME/.bun/bin:$HOME/.local/bin:$PATH" SUPERCOMPUTER_CONTROLLER=1
out=${SUPERCOMPUTER_OUTPUT_DIR:?native output required}
input="$PWD/focus-input"
mkdir -p "$out"
phase=preflight; tests=-1; compiler=-1; lint=-1; postcheck=-1; tests_started=0; compiler_started=0
finish(){
 local code=$?
 printf '{"schema":"b-writer-focused/v1","phase":"%s","testsExit":%s,"compilerExit":%s,"commitlintExit":%s,"sourcePostcheckExit":%s,"testInvocations":%s,"compilerInvocations":%s,"fullMldrSearch":false,"retries":0,"exitCode":%s}\n' "$phase" "$tests" "$compiler" "$lint" "$postcheck" "$tests_started" "$compiler_started" "$code" > "$out/summary.json"
 (cd "$out"; find . -type f ! -name ARTIFACTS.sha256 -print0 | sort -z | xargs -0 sha256sum > ARTIFACTS.sha256)
}
trap finish EXIT
cp "$input/identity.json" "$input/SOURCE.sha256" "$input/VENDORS.sha256" "$input/commit-message.txt" "$input/gate.jobs.json" "$out/"
sha256sum -c "$input/SOURCE.sha256" > "$out/source-before.log" 2>&1
(cd "$input"; sha256sum -c VENDORS.sha256) > "$out/vendor-verification.log" 2>&1
bun=$(command -v bun)
bun_version=$("$bun" --version)
bun_hash=$(sha256sum "$bun" | cut -d' ' -f1)
printf '%s\n%s\n%s\n' "$bun" "$bun_version" "$bun_hash" > "$out/runtime.txt"
[[ "$bun_version" == 1.4.3 && "$bun_hash" == 7ce7d6b654eddeec20afddf2396317fba6dc19ab52788a27e894e1806bf8f24b ]] || { echo 'selected Bun differs from the bound runtime pin' >> "$out/runtime.txt"; exit 65; }
phase=dependency-setup
tar -xf "$input/gdp-ts.tar"
tar -xf "$input/handwired.tar"
timeout --foreground --signal=TERM --kill-after=5s 120s bun install --frozen-lockfile --ignore-scripts > "$out/install.log" 2>&1
cp node_modules/typescript/package.json "$out/typescript-package.json"
for key in ${!GDP_@}; do unset "$key"; done
bun -e 'for (const [k,v] of Object.entries(await Bun.file("research/track-m/section51-closing-feedback/writer-flags.json").json())) console.log(k+"="+v)' > "$out/profile.env"
while IFS='=' read -r key value; do export "$key=$value"; done < "$out/profile.env"
# K already owns its scope/cut regression gate. These tests are B's changed
# controller, write-only serialization, external sampler and native parity.
test_files=(research/track-m/section51-closing-feedback/graph-capsule.test.ts research/track-m/section51-closing-feedback/memory-sampler.test.ts research/track-m/section51-closing-feedback/writer-parity.test.ts research/track-m/section51-closing-feedback/native-metadata.test.ts research/track-m/section51-closing-feedback/driver-owner.test.ts research/track-m/section51-closing-feedback/phase-status.test.ts core/count-recipe-controller.test.ts)
printf '%s\n' "${test_files[@]}" > "$out/test-files.txt"
phase=tests; tests_started=1
set +e
timeout --foreground --signal=TERM --kill-after=5s 300s bun test --timeout 240000 "${test_files[@]}" > "$out/tests.log" 2>&1
tests=$?
set -e
phase=compiler; compiler_started=1
compiler_files=(core/count-proof-scope.ts core/count-recipe-controller.ts core/count-recovery/conditional-proof.ts core/counts.ts core/trace-clock.ts core/work-admission.ts kernel/kernel.ts kernel/prove.ts research/track-m/section51-closing-feedback/*.ts research/track-m/section51-supplier-timed/*.ts "${test_files[@]}")
printf '%s\n' "${compiler_files[@]}" > "$out/compiler-files.txt"
set +e
timeout --foreground --signal=TERM --kill-after=5s 240s bun node_modules/typescript/bin/tsc --noEmit --allowImportingTsExtensions --moduleResolution bundler --target ES2022 --module ESNext --lib ESNext,DOM,DOM.Iterable --types bun,@webgpu/types --skipLibCheck --strict --noImplicitReturns --noFallthroughCasesInSwitch --noUncheckedIndexedAccess "${compiler_files[@]}" > "$out/compiler.log" 2>&1
compiler=$?
phase=commitlint
bash research/lane-i/combined-next/commitlint.sh "$input" > "$out/commitlint.log" 2>&1
lint=$?
sha256sum -c "$input/SOURCE.sha256" > "$out/source-after.log" 2>&1
postcheck=$?
set -e
phase=complete
if [[ "$tests" == 0 && "$compiler" == 0 && "$lint" == 0 && "$postcheck" == 0 ]]; then exit 0; else exit 1; fi
