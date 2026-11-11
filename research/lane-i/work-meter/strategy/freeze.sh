#!/usr/bin/env bash
set -euo pipefail
out=${1:?usage: freeze.sh NEW_DIRECTORY}
test ! -e "$out"
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
base=b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3
pin=aeef60912e189573eb24e658af7e915109a971d2
strategy=$(git -C "$root" rev-parse 37d006af^{commit})
git -C "$root" cat-file -e "$base^{commit}"
git -C "$root" cat-file -e "$pin^{commit}"
mkdir -p "$out"
# One pinned tree's objects, excluding the already-restored base; no mutable branch tips.
git -C "$root" rev-list --objects --no-object-names --max-count=1 "$pin" --not "$base" |
 git -C "$root" pack-objects --stdout > "$out/calibration-source.pack"
git -C "$root" diff --binary "$base" "$strategy" -- core kernel lean-kernel scripts/test-shards.ts research/protocols/ic3syn research/track-m > "$out/strategy.patch"
for file in prepare.ts resolve.ts instrument.ts meter-fixture.source path-coverage.source; do
 cp "$root/research/lane-i/work-meter/strategy/$file" "$out/$file"
done
cp "$root/research/lane-i/work-meter/complete/instrument-ast.ts" "$out/"
printf '{"base":"%s","pin":"%s","strategy":"%s","scope":"research composition only; no W or source admission"}\n' "$base" "$pin" "$strategy" > "$out/freeze.json"
(cd "$out"; sha256sum calibration-source.pack strategy.patch prepare.ts resolve.ts instrument.ts instrument-ast.ts meter-fixture.source path-coverage.source freeze.json > SHA256SUMS)
printf 'Frozen strategy inputs: %s\n' "$out"
