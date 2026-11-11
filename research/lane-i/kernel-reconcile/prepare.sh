#!/usr/bin/env bash
set -euo pipefail
out=${1:?new output directory}; test ! -e "$out"; mkdir -p "$out"
repo=$(git rev-parse --show-toplevel); cd "$repo"
b=69b8ef2b; f=cd671ac1; base=b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3
for side in B F; do
 ref=$b; test "$side" = B || ref=$f
 git rev-list --objects --no-object-names -n 1 "$ref" --not "$base" | git pack-objects --stdout > "$out/$side.pack"
done
# One common overlay. No branch, working tree, or production file is changed.
readme=$(mktemp); trap 'rm -f "$readme" "$out/index-B" "$out/index-F" "$out/index-docs"' EXIT
if test $# -gt 1; then cp "$2" "$readme"; else
 export GIT_INDEX_FILE="$out/index-docs"; git read-tree "$f"
 git apply --cached --include=lean-kernel/README.md research/lane-i/kernel-reconcile/F.patch
 git show :lean-kernel/README.md > "$readme"; unset GIT_INDEX_FILE
fi
readme_blob=$(git hash-object -w "$readme")
for side in B F; do
 ref=$b; test "$side" = B || ref=$f
 export GIT_INDEX_FILE="$out/index-$side"; git read-tree "$ref"
 for spec in "$f:kernel/cdcl.ts" "$f:kernel/cdcl-root.test.ts" "$b:kernel/frame-cut.test.ts" "$b:lean-kernel/emit.ts"; do
  path=${spec#*:}; blob=$(git rev-parse "$spec"); git update-index --add --cacheinfo "100644,$blob,$path"
 done
 git update-index --add --cacheinfo "100644,$readme_blob,lean-kernel/README.md"
 tree=$(git write-tree)
 git diff --binary "$ref" "$tree" -- kernel lean-kernel > "$out/$side.patch"
 printf '%s %s %s %s\n' "$side" "$tree" "$(git rev-parse "$tree:kernel")" "$(git rev-parse "$tree:lean-kernel")" >> "$out/trees.txt"
 unset GIT_INDEX_FILE
done
cp research/lane-i/kernel-reconcile/condition-columns.test.source "$out/"
(cd "$out"; sha256sum B.pack F.pack B.patch F.patch trees.txt condition-columns.test.source > SHA256SUMS)
