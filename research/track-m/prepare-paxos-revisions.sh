#!/usr/bin/env bash
# OUT followed by revisions or alias=revision; main is never inferred from HEAD.
set -euo pipefail
out="$1"; shift; mkdir -p "$out"
base=6a3874d3
git archive --format=tar -o "$out/main.tar" "$base"
git rev-parse "$base" > "$out/revision.txt"
for item in "$base" "$@"; do
 name="${item%%=*}"; rev="${item#*=}"
 [[ "$name" =~ ^[a-zA-Z0-9][a-zA-Z0-9_.-]*$ ]] || { echo "invalid snapshot name: $name" >&2; exit 2; }
 git rev-parse --verify --end-of-options "$rev^{commit}" >/dev/null
 git diff --binary "$base" "$rev" -- . ':(exclude)runs/**' > "$out/$name.patch"
done
(cd "$out" && shasum -a 256 main.tar > main.tar.sha256)
