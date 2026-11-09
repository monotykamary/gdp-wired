#!/usr/bin/env bash
# Submission validation is local and light; checks/proofs execute only on boat.
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
root=$(cd -- "$here/../.." && pwd)
input=${INV1758_INPUT:-/private/tmp/gdp-wired-inv1758-input-v1}
frozen=${INV1758_FROZEN:-/tmp/gdp-wired-incl-resume-84a7a672}
output=${INV1758_OUTPUT:-$root/runs/mldr-rows-guard-v3}
test -f "$input/family.json"
test -f "$input/provenance.json"
printf '%s  %s\n' f14f538ea14763ced6f8aac5227ae9bc9fbc6dd18acea4f150cbaadd3eeca639 "$input/family.json" | shasum -a 256 -c -
for file in "$frozen/core/counts.ts" /private/tmp/gdp-incl-preflight-8e7e8630/apply.sh /private/tmp/gdp-incl-demand-ac7eacfe/apply.sh /private/tmp/gdp-incl-flags-9124348d/apply.sh /private/tmp/gdp-wired-inv1758-early-v1/install-early.ts /private/tmp/gdp-wired-inv1758-guard-v2/guard-pair.sh /private/tmp/gdp-wired-inv1758-guard-v2/member-inclusions.after.txt /private/tmp/gdp-wired-inv1758-guard-v2/member-inclusions.test.txt; do test -f "$file"; done
exec supercomputer --repo "$frozen" run --jobs "$here/guard-jobs.json" --class submission --timing --vm-type large \
 --data /private/tmp/gdp-incl-preflight-8e7e8630:lane-e-preflight \
 --data /private/tmp/gdp-incl-demand-ac7eacfe:lane-e-demand \
 --data /private/tmp/gdp-incl-flags-9124348d:lane-e-flags \
 --data "$input:lane-e-rows" \
 --data /private/tmp/gdp-wired-inv1758-early-v1:row-early \
 --data /private/tmp/gdp-wired-inv1758-guard-v2:row-guard \
 --out "$output"
