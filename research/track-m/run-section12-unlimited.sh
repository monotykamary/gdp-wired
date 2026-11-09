#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
name="$1"
case "$name" in star) target='Inv*';; overlap) target='Inv2973';; *) exit 2;; esac
work=$(mktemp -d /tmp/section12-unlimited-XXXXXX)
out="$work/results"
mkdir -p "$out" "$work/frozen"
trap 'status=$?; shopt -s nullglob; files=("$out"/*); if ((${#files[@]})); then bun "$root/research/track-m/pack-section10-archive.ts" "${files[@]}"; fi; rm -rf "$work"; exit "$status"' EXIT
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
(cd source-input && sha256sum -c archive.sha256)
tar xzf source-input/source.tar.gz -C "$work/frozen"
cp -a research/track-m/. "$work/frozen/research/track-m/"
ln -s "$root/node_modules" "$work/frozen/node_modules"
ln -s "$root/vendor" "$work/frozen/vendor"
cd "$work/frozen"
bun research/track-m/section12-integrity.ts before "$out/source-before.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section10-diagnostic.ts family > "$out/instrumentation-base.json"
TRACK_M_DISPOSABLE_PROFILE=1 bun research/track-m/install-section12-unlimited.ts > "$out/instrumentation-ops.json"
bun research/track-m/section12-integrity.ts after "$out/source-before.json" > "$out/integrity.json"
# Outer process safety watchdog only. A kill is censored, never a proof failure.
timeout -s KILL 3600 bun research/track-m/run-section12-unlimited.ts "$root/replay-input/input.json" "$target" "$out" > "$out/probe.log" 2>&1
