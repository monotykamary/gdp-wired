#!/usr/bin/env bash
# File materialization only. Do not edit a frozen directory while a batch uses it.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
base=${1:?usage: bash research/lane-i/work-meter/f4/freeze.sh /absolute/new-snapshot}
case "$base" in /*) ;; *) printf 'snapshot path must be absolute\n' >&2; exit 2 ;; esac
test ! -e "$base"
cd "$root"
data="$base/data"
mkdir -p "$base/runner" "$data"/{recovery-input,complete-input,ledger-input,coverage-input,validation-input,f3-input,f4-input,artifact-input}
# About 147 MB once, reused for every batch. No source worktree or per-job archive.
cp research/lane-i/work-meter/recovery/{root.pack,module-0.pack,module-1.pack,manifest.json,materialize.ts,compose.ts,final-gate-common.ts} "$data/recovery-input/"
cp research/lane-i/work-meter/complete/{identity.json,candidate.patch} "$data/complete-input/"
cp research/lane-i/work-meter/ledger/{identity.json,candidate.patch,boundaries.patch} "$data/ledger-input/"
cp research/lane-i/work-meter/coverage/{bitsets.source,bitsets-meter.test.source,canonicalization.ts,canonical-meter.test.source} "$data/coverage-input/"
printf 'created by materialize.ts\n' > "$data/validation-input/.keep"
cp research/lane-i/work-meter/f3/facade.source "$data/f3-input/"
cp research/lane-i/work-meter/f4/{pilot.ts,census.source} "$data/f4-input/"
cp runs/lane-i/complete-artifact/complete-ast-artifact.log "$data/artifact-input/"
cp research/lane-i/work-meter/f4/pilot.jobs.json "$base/pilot.jobs.json"
cp research/lane-i/work-meter/f4/runner.toml.source "$base/runner/supercomputer.toml"
cp research/lane-i/work-meter/f4/runner-hooks.py.source "$base/runner/hooks.py"
printf '%s\n' "$root" > "$base/runner/source-root.txt"
cp research/lane-i/work-meter/recovery/RUNNER-COMMIT.txt "$base/runner/COMMIT.txt"
cp research/lane-i/work-meter/recovery/RUNNER-COMMIT.txt "$data/recovery-input/RUNNER-COMMIT.txt"
cd "$base/runner"
git init --quiet
git add supercomputer.toml hooks.py source-root.txt COMMIT.txt
GIT_EDITOR=true git commit -q -F COMMIT.txt
git rev-parse HEAD
printf 'FROZEN_CENSUS_INPUTS %s\n' "$base"
