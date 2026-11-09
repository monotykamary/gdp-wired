#!/usr/bin/env bash
set -euo pipefail
for group in 0 1 2; do
  out="runs/lane-i/paxos/ryzen/group-$group"
  echo "PAXOS_GROUP_BEGIN $group"
  supercomputer --repo /private/tmp/lane-i-paxos-runner.djtUt9 run --jobs "research/lane-i/regressions/paxos-ryzen-$group.jobs.json" --out "$out" --class submission --timing --vm-type large --data /private/tmp/lane-i-paxos-ryzen-data.9b5PMj:frozen-paxos
  PAXOS_TARGET_CPU='AMD Ryzen 9 9950X 16-Core Processor' bun research/lane-i/regressions/paxos-cohort-audit.ts "$out" "research/lane-i/regressions/paxos-ryzen-$group.jobs.json" "research/lane-i/regressions/paxos-ryzen-points-$group.json" > "$out/audit.stdout.json"
  echo "PAXOS_GROUP_AUDITED $group"
done
