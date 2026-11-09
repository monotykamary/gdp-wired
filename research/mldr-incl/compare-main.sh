#!/usr/bin/env bash
# Both sides execute checked git archives, never the surrounding mutable upload.
set -euo pipefail
kind=${1:?}; id=${2:?}; repeat=${3:?}; first=${4:?}
base_sha=${5:?}; cand_sha=${6:?}; base_hash=${7:?}; cand_hash=${8:?}
[[ "$kind" =~ ^(ic3syn|duoai|broken)$ && "$id" =~ ^[a-z0-9_]+$ && "$repeat" =~ ^[1-3]$ && "$first" =~ ^(base|cand)$ ]] || exit 2
[[ "$base_sha" =~ ^[0-9a-f]{40}$ && "$cand_sha" =~ ^[0-9a-f]{40}$ && "$base_hash" =~ ^[0-9a-f]{64}$ && "$cand_hash" =~ ^[0-9a-f]{64}$ && "$base_sha" != "$cand_sha" ]] || exit 2
root=$PWD; scratch="${TMPDIR:-/tmp}/mldr-incl-pair-$$"; mkdir -p "$scratch"
trap 'rm -rf "$scratch"' EXIT
for side in base cand; do
 archive="$root/gate-input/$side.tar"; want_sha=$base_sha; want_hash=$base_hash
 if [[ "$side" == cand ]]; then want_sha=$cand_sha; want_hash=$cand_hash; fi
 actual_hash=$(sha256sum "$archive"); actual_hash=${actual_hash%% *}
 [[ "$actual_hash" == "$want_hash" ]] || { echo "$side archive hash mismatch"; exit 2; }
 [[ "$(git get-tar-commit-id <"$archive")" == "$want_sha" ]] || { echo "$side archive revision mismatch"; exit 2; }
 mkdir -p "$scratch/$side"; tar xf "$archive" -C "$scratch/$side"
 (cd "$scratch/$side" && bash "$root/research/track-m/prepare-vendors.sh" && test "$(git -C vendor/gdp-ts rev-parse HEAD)" = 0b6ebeeec827b05210f3acfa4149a70dda9a0de5 && test "$(git -C vendor/handwired rev-parse HEAD)" = d47141cce2caf5b86b0c2c0c372a5174f424bc15 && bun install --frozen-lockfile >/dev/null 2>&1)
done
echo "PAIR source base=$base_sha cand=$cand_sha base_archive=$base_hash cand_archive=$cand_hash"
harness=research/protocols/ic3syn/run.ts; skip=broken
if [[ "$kind" == duoai ]]; then harness=research/protocols/run.ts; skip=broken,given; fi
if [[ "$kind" == broken ]]; then skip=search; fi
other=base; [[ "$first" != base ]] || other=cand
failed=0
for side in "$first" "$other"; do
 echo "PAIR begin side=$side suite=$kind id=$id repeat=$repeat base=$base_sha cand=$cand_sha"
 set +e
 (cd "$scratch/$side" && timeout -s KILL 60 bun "$harness" --ms 60000 --only "$id" --skip "$skip") >"$scratch/out" 2>"$scratch/err"
 status=$?
 set -e
 head -c 200000 "$scratch/out"
 if [[ "$status" != 0 && "$status" != 124 && "$status" != 137 ]]; then tail -c 5000 "$scratch/err"; failed=1; fi
 echo "PAIR end side=$side suite=$kind id=$id repeat=$repeat base=$base_sha cand=$cand_sha exit=$status"
done
exit "$failed"
