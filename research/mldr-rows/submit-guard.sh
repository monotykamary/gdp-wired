#!/usr/bin/env bash
# Submission validation is local and light; checks/proofs execute only on boat.
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
root=$(cd -- "$here/../.." && pwd)
# Prepared input directories, rooted at this checkout unless explicitly overridden.
artifacts=${INV1758_ARTIFACTS:-$root/inputs/mldr-rows}
input=${INV1758_INPUT:-$artifacts/input}
frozen=${INV1758_FROZEN:-$artifacts/frozen}
preflight=${INV1758_PREFLIGHT:-$artifacts/preflight}
demand=${INV1758_DEMAND:-$artifacts/demand}
flags=${INV1758_FLAGS:-$artifacts/flags}
early=${INV1758_EARLY:-$artifacts/early}
guard=${INV1758_GUARD:-$artifacts/guard}
output=${INV1758_OUTPUT:-$root/runs/mldr-rows-guard-v3}
jobs=${INV1758_JOBS:-$here/guard-jobs.json}
test -f "$input/family.json"
test -f "$input/provenance.json"
printf '%s  %s\n' f14f538ea14763ced6f8aac5227ae9bc9fbc6dd18acea4f150cbaadd3eeca639 "$input/family.json" | shasum -a 256 -c -
for file in "$frozen/core/counts.ts" "$preflight/apply.sh" "$demand/apply.sh" "$flags/apply.sh" "$early/install-early.ts" "$guard/guard-pair.sh" "$guard/member-inclusions.after.txt" "$guard/member-inclusions.test.txt"; do test -f "$file"; done
exec supercomputer --repo "$frozen" run --jobs "$jobs" --class submission --timing --vm-type large \
 --data "$preflight:lane-e-preflight" \
 --data "$demand:lane-e-demand" \
 --data "$flags:lane-e-flags" \
 --data "$input:lane-e-rows" \
 --data "$early:row-early" \
 --data "$guard:row-guard" \
 --out "$output"
