#!/usr/bin/env bash
# Boat snapshots omit the contents of uninitialized gitlinks. Fetch only the
# revisions pinned by this Track M worktree, in the remote job's private copy.
set -euo pipefail
export GIT_TERMINAL_PROMPT=0
fetch_pin() {
  local dest="$1" url="$2" rev="$3" sentinel="$4"
  if [[ -f "$dest/$sentinel" ]]; then return; fi
  mkdir -p "$dest"
  git -C "$dest" init -q
  git -C "$dest" -c credential.helper= fetch --quiet --depth=1 "$url" "$rev"
  git -C "$dest" -c advice.detachedHead=false checkout --quiet --detach FETCH_HEAD
}
fetch_pin vendor/gdp-ts https://github.com/rauchg/gdp-ts.git 0b6ebeeec827b05210f3acfa4149a70dda9a0de5 src/index.ts
fetch_pin vendor/handwired https://github.com/monotykamary/handwired.git d47141cce2caf5b86b0c2c0c372a5174f424bc15 src/json-search/loop-program.ts
