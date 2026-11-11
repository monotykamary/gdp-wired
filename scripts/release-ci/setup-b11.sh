#!/usr/bin/env bash
set -euo pipefail
meta=$(realpath "$1"); dest=$2
restore_git() {
  local directory=$1 role=$2
  git -C "$directory" init -q
  git -C "$directory" -c advice.addEmbeddedRepo=false add -f -A
  test "$(git -C "$directory" write-tree)" = "$(<"$meta/$role.tree")"
  local sha
  sha=$(git -C "$directory" hash-object -t commit -w "$meta/$role.commit")
  test "$sha" = "$(<"$meta/$role.sha")"
  printf '%s\n' "$sha" > "$directory/.git/shallow"
  git -C "$directory" update-ref HEAD "$sha"
}
mkdir -p "$dest"
tar -xf base-archive/base.tar -C "$dest"
for name in handwired gdp-ts; do
  mkdir -p "$dest/vendor/$name"
  tar -xf "source-archives/$name.tar" -C "$dest/vendor/$name"
  restore_git "$dest/vendor/$name" "$name"
done
git -C "$dest" apply --allow-empty "$meta/candidate.patch"
restore_git "$dest" main
git -C "$dest" submodule init
git -C "$dest" submodule absorbgitdirs
test -z "$(git -C "$dest" status --porcelain --untracked-files=all)"
printf 'CLEAN_CHECKOUT_HEAD '; git -C "$dest" rev-parse HEAD
printf 'CLEAN_CHECKOUT_TREE '; git -C "$dest" rev-parse HEAD^{tree}
git -C "$dest" submodule status --recursive
