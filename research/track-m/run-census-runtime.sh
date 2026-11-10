#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
plan="${1:-research/track-m/census-integrity-runtime-plan.json}"
work=$(mktemp -d /tmp/census-runtime-XXXXXX)
out="$work/results"
mkdir -p "$out"
trap 'status=$?; if ! bun "$root/research/track-m/summarize-census-cpu.ts" "$out"; then status=1; fi; shopt -s nullglob; files=(); critical=(); for f in "$out"/*; do case "$f" in *.cpuprofile) ;; */source-manifest.json|*/runtime.json|*/measurements.json) critical+=("$f") ;; *) files+=("$f") ;; esac; done; if ((${#files[@]} + ${#critical[@]})); then bun "$root/research/track-m/pack-section7-receipts.ts" "${files[@]}" "${critical[@]}"; fi; rm -rf "$work"; exit "$status"' EXIT
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
bun run check
bun test research/track-m/census-integrity-audit.test.ts research/track-m/phase-census-meter.test.ts
# Verify the engine recognizes each isolated runtime option, not merely its env var.
BUN_JSC_dumpOptions=1 bun -e '0' > "$out/default-options.log" 2>&1
BUN_JSC_dumpOptions=1 BUN_JSC_logGC=1 bun -e '0' > "$out/gc-logging-options.log" 2>&1
grep -Eq "logGC[[:space:]]*=[[:space:]]*1" "$out/gc-logging-options.log"
for option in useConcurrentJIT useConcurrentGC useFTLJIT; do
 env BUN_JSC_dumpOptions=1 "BUN_JSC_${option}=false" bun -e '0' > "$out/$option-options.log" 2>&1
 grep -Eq "$option[[:space:]]*=[[:space:]]*false" "$out/$option-options.log"
done
(cd integrity-input && sha256sum -c archives.sha256)
for name in census tf1; do
 mkdir -p "$work/$name"
 tar xzf "integrity-input/$name.tar.gz" -C "$work/$name"
 rm -rf "$work/$name/node_modules" "$work/$name/vendor"
 ln -s "$root/node_modules" "$work/$name/node_modules"
 ln -s "$root/vendor" "$work/$name/vendor"
done
bun research/track-m/prepare-census-integrity.ts "$work" "$root" "$out"
bun research/track-m/run-census-integrity.ts "$work" "$root/replay-input/input.json" "$out" "$plan"
