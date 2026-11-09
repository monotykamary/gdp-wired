#!/usr/bin/env bash
# Diagnostic F-only overlay, not a main-vs-candidate final gate.
set -euo pipefail
rep=${1:?repeat}; order=${2:?before|after}
sha256sum controls.tar.gz
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
work=$(mktemp -d "$HOME/lane-f-original-XXXXXX")
trap 'status=$?; bash research/track-m/pack-section18-archive.sh "$work"; exit "$status"' EXIT
mkdir -p "$work/control" "$work/candidate"
tar xzf controls.tar.gz -C "$work/control"
files=(core/count-cases.ts core/count-recovery/row-cases.ts core/count-recovery/derivability-closure.ts)
for f in "${files[@]}"; do mkdir -p "$work/candidate/$(dirname "$f")"; cp "$f" "$work/candidate/$f"; done
for side in "$order" "$([[ "$order" == before ]] && echo after || echo before)"; do
 for f in "${files[@]}"; do
  if [[ "$side" == before ]]; then cp "$work/control/$f" "$f"; else cp "$work/candidate/$f" "$f"; fi
 done
 echo "LANE_F_ORIGINAL_BEGIN $rep $side baseline-overlay=d4479299 candidate-source=78eedf50"
 sha256sum "${files[@]}"
 set +e
 GDP_INFER_TRACE=2 timeout 75s bun research/protocols/ic3syn/run.ts --ms 60000 --only mldr --skip broken > "$work/$side.log" 2>&1
 status=$?
 set -e
 grep '^{' "$work/$side.log" || true
 tail -n 3 "$work/$side.log"
 echo "LANE_F_ORIGINAL_END $rep $side status=$status"
 [[ $status == 0 ]] || exit "$status"
done
