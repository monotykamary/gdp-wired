#!/usr/bin/env bash
# Reusable collector for an EXPLICITLY AUTHORIZED exact-pin software gate.
# Preparation only: this file does not submit a job or authorize a retry.
# Input contract: sealed archives/profile and messages/index.txt (one SHA/line).
set -euo pipefail
input=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
out=${SUPERCOMPUTER_OUTPUT_DIR:?}
mkdir -p "$out/logs" "$out/source"
cp "$input/manifest.json" "$out/input-manifest.json"
cp "$input/SHA256SUMS" "$out/input-SHA256SUMS"
[[ -s "$input/messages/index.txt" ]]
(cd "$input" && sha256sum -c SHA256SUMS) > "$out/input-verification.log" 2>&1
for key in ${!GDP_@}; do unset "$key"; done
export GDP_WORK_FULL=1 GDP_WORK_STEPS=0 GDP_COUNT_REACHABILITY_SCREEN=0
export GDP_COUNT_DEFER_CHECKS=0 GDP_COUNT_C2_REPLAY=0 GDP_COUNT_C2_LEMMAS=0
export GDP_WORK_WEIGHTS=$(< "$input/unit-weights.json")
export GIT_TERMINAL_PROMPT=0 SUPERCOMPUTER_CONTROLLER=1
export PATH="$HOME/.local/bin:$HOME/.bun/bin:$HOME/.elan/bin:$PATH"
bun=$HOME/.bun/bin/bun
[[ $("$bun" --version) == 1.4.3 ]]
[[ $(sha256sum "$bun" | cut -d ' ' -f 1) == 7ce7d6b654eddeec20afddf2396317fba6dc19ab52788a27e894e1806bf8f24b ]]
{ printf 'bun=%s\n' "$bun"; "$bun" --version; sha256sum "$bun"; env | LC_ALL=C sort | grep -E '^(GDP_|SUPERCOMPUTER_CONTROLLER=|PATH=)'; } > "$out/environment.txt"
scratch=$(mktemp -d /tmp/gdp-b-section46-gate.XXXXXX)
trap 'rm -rf -- "$scratch"' EXIT
for pin in top baseline-0fc baseline-b8; do
 mkdir -p "$scratch/$pin"
 tar -xzf "$input/$pin.tar.gz" -C "$scratch/$pin"
done
top=$scratch/top
printf 'phase\tstatus\texit_code\tseconds\tlog\n' > "$out/outcomes.tsv"
failures=0
run_phase(){
 local name=$1 dir=$2 limit=$3; shift 3
 local code=0 start end
 start=$(date +%s)
 (cd "$dir" && timeout --foreground --signal=TERM --kill-after=5s "${limit}s" "$@") > "$out/logs/$name.log" 2>&1 || code=$?
 end=$(date +%s)
 printf '%s\t%s\t%s\t%s\tlogs/%s.log\n' "$name" "$([[ $code == 0 ]] && echo EXITED_ZERO || echo EXITED_NONZERO)" "$code" "$((end-start))" "$name" >> "$out/outcomes.tsv"
 printf 'PHASE %s exit=%s seconds=%s\n' "$name" "$code" "$((end-start))"
 if [[ $code != 0 ]]; then failures=$((failures+1)); fi
 return 0
}
hash_source(){ (cd "$1" && find core kernel -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum); }
run_phase setup.install "$top" 300 "$bun" install --frozen-lockfile
install_code=$(awk -F '\t' '$1=="setup.install"{print $3}' "$out/outcomes.tsv")
run_phase setup.vendors "$top" 300 bash research/track-m/prepare-vendors.sh
vendors_code=$(awk -F '\t' '$1=="setup.vendors"{print $3}' "$out/outcomes.tsv")
if [[ $install_code != 0 || $vendors_code != 0 ]]; then
 for phase in test.acceptance test.owners test.cohort test.context-public baseline.0fc baseline.b8 typecheck lint; do
  printf '%s\tNOT_RUN_SETUP_FAILED\t-\t0\t-\n' "$phase" >> "$out/outcomes.tsv"
 done
 index=0
 while IFS= read -r sha || [[ -n "$sha" ]]; do
  [[ "$sha" =~ ^[0-9a-f]{40}$ ]] || exit 70
  index=$((index+1))
  printf 'commitlint.%s\tNOT_RUN_SETUP_FAILED\t-\t0\t-\n' "$index" >> "$out/outcomes.tsv"
 done < "$input/messages/index.txt"
 printf 'SETUP_FAILED; no test/compile result claimed\n' > "$out/FINAL.txt"
 exit 70
fi
for vendor in gdp-ts handwired; do git -C "$top/vendor/$vendor" rev-parse HEAD; done > "$out/vendor-pins.txt"
hash_source "$top" > "$out/source/top.before.sha256"
for pin in baseline-0fc baseline-b8; do
 base=$scratch/$pin
 ln -s "$top/node_modules" "$base/node_modules"
 for vendor in gdp-ts handwired; do rm -rf -- "$base/vendor/$vendor"; ln -s "$top/vendor/$vendor" "$base/vendor/$vendor"; done
 cp "$input/count-recipe-cohort.test.ts" "$base/core/count-recipe-cohort.test.ts"
 sha256sum "$base/core/count-recipe-cohort.test.ts" > "$out/source/$pin.overlay.sha256"
 hash_source "$base" > "$out/source/$pin.before.sha256"
done
(cd "$top" && "$bun" -e 'import {workLedger} from "./core/work-admission.ts"; console.log(JSON.stringify({weights:workLedger.snapshot().weights,root:workLedger.snapshot().rootBaseline}));') > "$out/native-weights.json"
# Each of these is one fresh OS process and only one test file.
run_phase test.acceptance "$top" 180 "$bun" test --timeout 120000 core/count-section46-acceptance.test.ts
run_phase test.owners "$top" 180 "$bun" test --timeout 120000 core/count-owner-budget.test.ts
run_phase test.cohort "$top" 180 "$bun" test --timeout 120000 core/count-recipe-cohort.test.ts
run_phase test.context-public "$top" 180 "$bun" test --timeout 120000 core/count-recipe-context-public.test.ts
# Historical observations, never qualification of the old pins.
run_phase baseline.0fc "$scratch/baseline-0fc" 180 "$bun" test --timeout 120000 core/count-recipe-cohort.test.ts
run_phase baseline.b8 "$scratch/baseline-b8" 180 "$bun" test --timeout 120000 core/count-recipe-cohort.test.ts
# Deliberately collect ALL requested phases even after test failures.
run_phase typecheck "$top" 240 "$bun" x tsc -p .
run_phase lint "$top" 240 "$bun" x oxlint --type-aware --deny-warnings --disable-nested-config .
index=0
while IFS= read -r sha || [[ -n "$sha" ]]; do
 [[ "$sha" =~ ^[0-9a-f]{40}$ ]] || exit 70
 index=$((index+1))
 # Match A's established gate: exact message bytes through stdin. Do not use
 # --edit/--from/--to, which require .git metadata absent from source archives.
 run_phase commitlint.$index "$top" 120 "$bun" x --bun @commitlint/cli@19.8.1 --config research/egraph/historical/commitlint.config.cjs < "$input/messages/$sha.txt"
done < "$input/messages/index.txt"
for pin in top baseline-0fc baseline-b8; do
 hash_source "$scratch/$pin" > "$out/source/$pin.after.sha256"
 code=0; cmp "$out/source/$pin.before.sha256" "$out/source/$pin.after.sha256" > "$out/logs/source-$pin.log" 2>&1 || code=$?
 printf 'source.%s\t%s\t%s\t0\tlogs/source-%s.log\n' "$pin" "$([[ $code == 0 ]] && echo EXITED_ZERO || echo EXITED_NONZERO)" "$code" "$pin" >> "$out/outcomes.tsv"
 if [[ $code != 0 ]]; then failures=$((failures+1)); fi
done
printf 'Raw nonzero phases: %s\nN3 intentional flat RED is not skipped. Historical rows are observations only.\n' "$failures" > "$out/FINAL.txt"
cat "$out/outcomes.tsv"
if [[ $failures != 0 ]]; then exit 1; fi
