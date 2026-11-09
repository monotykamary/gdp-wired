#!/usr/bin/env bash
# A pinned current-main pair on one large VM. No proof or wall budget is raised.
set -euo pipefail
kind=${1:?}; id=${2:?}; first=${3:?}; root=$PWD
base="${TMPDIR:-/tmp}/mldr-incl-main-$$"; log="${TMPDIR:-/tmp}/mldr-incl-pair-$$"
trap 'rm -rf "$base"; rm -f "$log.out" "$log.err"' EXIT
(cd baseline-input && sha256sum -c main.tar.sha256)
revision=$(<baseline-input/revision.txt)
[[ "$revision" == b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c ]] || { echo wrong-main-revision; exit 2; }
mkdir -p "$base"; tar xf baseline-input/main.tar -C "$base"
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null 2>&1
(cd "$base" && bash "$root/research/track-m/prepare-vendors.sh" && bun install --frozen-lockfile >/dev/null 2>&1)
harness=research/protocols/ic3syn/run.ts; skip=broken; phase=search
if [[ "$kind" == duoai ]]; then harness=research/protocols/run.ts; skip=broken,given; fi
if [[ "$kind" == broken ]]; then skip=search; phase=broken; fi
other=base; [[ "$first" != base ]] || other=cand
failed=0
for side in "$first" "$other"; do
 dir=$root; [[ "$side" != base ]] || dir=$base
 echo "PAIR begin side=$side phase=$phase id=$id baseline=$revision"
 set +e
 (cd "$dir" && timeout -s KILL 60 bun "$harness" --ms 60000 --only "$id" --skip "$skip") >"$log.out" 2>"$log.err"
 status=$?
 set -e
 head -c 200000 "$log.out"
 if [[ "$status" != 0 && "$status" != 124 && "$status" != 137 ]]; then tail -c 5000 "$log.err"; failed=1; fi
 echo "PAIR end side=$side phase=$phase exit=$status"
done
exit "$failed"
