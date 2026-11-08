#!/usr/bin/env bash
# Run the reviewer's unchanged harness and all twelve unchanged substitutions in owned boat scratch.
set -euo pipefail
work=$(mktemp -d /tmp/track-k-review-mutants.XXXXXX)
trap 'rm -rf "$work"' EXIT
cp -a . "$work/tree"
cd "$work/tree"
cp research/track-k/review-source/review-run.ts.txt review-run.ts
cp research/track-k/review-source/review-mutants.json review-mutants.json
bun install --frozen-lockfile >/dev/null
TC=~/.elan/toolchains/leanprover--lean4---v4.34.0
export PATH="$TC/bin:$PATH"
export LEAN_PATH="$PWD/lean-kernel:$TC/lib/lean"
cd lean-kernel
for mod in Cert Kernel Progress StepLaw Steps Sets Count CountMachine; do lean -o "$mod.olean" "$mod.lean"; done
cd ..
bun review-run.ts
bun -e 'const assert=require("node:assert/strict"); const rows=JSON.parse(await Bun.file("review-results/results.json").text()); assert.equal(rows.length,13); assert(rows[0].id==="baseline"&&rows[0].survived); assert.deepEqual(rows.slice(1).filter(r=>r.survived).map(r=>r.id),["M03-slice-upper-inclusive"]); console.log("VERIFIED_MUTANT_MATRIX="+JSON.stringify(rows));'
