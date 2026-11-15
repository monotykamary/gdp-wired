#!/usr/bin/env bash
set -uo pipefail
: "${SUPERCOMPUTER_OUTPUT_DIR:?native output directory required}"
out=$SUPERCOMPUTER_OUTPUT_DIR
mkdir -p "$out"
# This is an uncounted correctness gate, not a canonical benchmark/profile run.
while IFS= read -r key; do unset "$key"; done < <(compgen -e | grep '^GDP_' || true)
if [[ "${B_STALE_BINDER_MODE:?missing mode}" == off ]]; then export GDP_MEMO_ALPHA=0; fi
printf '%s\n' "${B_STALE_BINDER_SOURCE:?missing source}" > "$out/source-commit.txt"
sha256sum kernel/prove.ts kernel/prove-memo.test.ts research/track-m/stale-binder-regression.ts > "$out/source-files.sha256"
bun research/track-m/repro-stale-binder.ts > "$out/repro.json" 2> "$out/repro.stderr"
repro=$?
bun test kernel/prove-memo.test.ts > "$out/unit.log" 2>&1
unit=$?
bun research/track-m/stale-binder-regression.ts > "$out/protocols.log" 2>&1
protocols=$?
printf '{"mode":"%s","reproExit":%s,"unitExit":%s,"protocolsExit":%s,"scope":"UNCOUNTED_KIND_LAWS_ONLY"}\n' "$B_STALE_BINDER_MODE" "$repro" "$unit" "$protocols" > "$out/gate.json"
(cd "$out" && find . -type f ! -name ARTIFACTS.sha256 -print0 | sort -z | xargs -0 sha256sum > ARTIFACTS.sha256)
[[ $repro == 0 && $unit == 0 && $protocols == 0 ]]
