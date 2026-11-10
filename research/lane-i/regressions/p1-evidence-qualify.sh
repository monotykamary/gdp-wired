#!/usr/bin/env bash
set -euo pipefail
cp -a frozen-paxos/. .
root=$(mktemp -d /tmp/lane-i-p1-evidence.XXXXXX)
trap 'rm -rf "$root"' EXIT
bun regression-driver/p1-evidence-source.ts "$root"
cp -a final-overlay/. "$root/"
cp -a final-input "$root/evidence-input"
cd "$root"
cp evidence-input/confirmation/audit.json evidence-input/confirmation/expected.json
cp evidence-input/timeouts/audit.json evidence-input/timeouts/expected.json
bun install --frozen-lockfile >/dev/null
bun run check
bun test ./research/lane-i/regressions/p1-scheduling-audit.test.ts
bun research/lane-i/regressions/p1-confirm-audit.ts evidence-input/confirmation evidence-input/family.json
bun research/lane-i/regressions/timeout-pairs-audit.ts evidence-input/timeouts
cmp evidence-input/confirmation/expected.json evidence-input/confirmation/audit.json
cmp evidence-input/timeouts/expected.json evidence-input/timeouts/audit.json
echo P1_FINAL_EVIDENCE_PASS
