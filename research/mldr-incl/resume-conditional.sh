#!/usr/bin/env bash
# Research-only conditional replay. The helpers are assumed, not proved here.
set -euo pipefail
bash research/track-m/prepare-vendors.sh
bun install --frozen-lockfile >/dev/null
# Never start a new proof experiment on an unchecked integrated source.
bun run check
bun test research/mldr-incl/pack-production.test.ts
tmp=$(mktemp -d /tmp/incl-resume.XXXXXX)
trap 'rm -rf "$tmp"' EXIT
GENERATOR_REV=${GENERATOR_REV:?source revision required} MLDR_INCL_FAMILY_OUT="$tmp/family-source.json" bun research/mldr-incl/capture-generation.ts mldr
MLDR_INCL_VARIANT=resume-integrated MLDR_INCL_FAMILY=generated timeout -s KILL 45 bun research/mldr-incl/conditional-safety.ts "$tmp/family-source.json" 2700 no
set +e
MLDR_INCL_VARIANT=resume-integrated MLDR_INCL_FAMILY=generated DUMP_DIR="$tmp" DUMP_MIN=0 DUMP_N=100000 DUMP_ALL=1 timeout -s KILL 45 bun --preload ./research/query/dump.ts --preload ./research/track-p/capture.ts --preload ./research/mldr-incl/premise-trace.ts research/mldr-incl/conditional-safety.ts "$tmp/family-source.json" 6000 no
probe=$?
set -e
replay=0
if test -f "$tmp/production-proof.json"; then
 # A separate process rebuilds START and STEP from the machine, laws and instances.
 bun research/mldr-incl/inspect-production.ts "$tmp/production-proof.json" || replay=$?
else
 echo 'NO_PRODUCTION_PROOF_TO_REPLAY'
fi
# Keep every required artifact or fail loudly; no size-based omission of a certificate.
bun research/mldr-incl/pack-production.ts "$tmp"
if test "$probe" -ne 0; then exit "$probe"; fi
exit "$replay"
