# Exact GENERATION row handoff to Fable

Committed runner/runtime pin: `9312f3ec2a9dd6ee8c527e90752fabdf55741c78`.
This is I's integrated line (G1 source retained), with NO core/kernel changes
in the runner commit. Static type/lint and commitlint pass; no GEN run made.

## Exact immutable data

Directory `/tmp/lane-i-generation-contract`, mount into the worker as data:

| file | SHA256 |
|---|---|
|source.tar|e8252b2731e8c5fd903e9a0a52e93eb7dc4514d83c22438c90823985314ddef6|
|gdp-ts.tar|68994527332b5abd3bf4c523135fb00fca7846a95451abb9e706bddaa9f1b42d|
|handwired.tar|242f2ad56c448edd61ee8ad7f1680018fbf6378da3ffbbf21d214930327f399e|

Extract all three into the same source root, then use the frozen-lockfile
install and Bun executable/OS closure from D's frozen anchor kit. No external
MLDR law fixture: the committed model/declared laws are used directly.

## Command inside that root

```
env -i PATH="$PATH" HOME="$HOME" \
 GDP_WORK_FULL=1 GDP_WORK_STEPS=0 GDP_COUNT_FRAMES=1 \
 GDP_COUNT_REJECTIONS=1 GDP_COUNT_STRATEGIES=1 GDP_COUNT_TIERS=1 \
 GDP_REQUEST_QUOTIENT=1 GDP_COUNT_ROW_DEFER_CHECKS=1 \
 GENERATION_SOURCE_PIN=9312f3ec2a9dd6ee8c527e90752fabdf55741c78 \
 bun research/lane-i/generation-row/runner.ts \
 --expect /data/generation-identity.json --out /output/generation
```

Exactly D's8-entry6f05 vector. All other GDP flags must be absent (runner
rejects extras), including F/C2/final-defer/scheduler flags. Fixed public
search work ceiling225000000 is historical provisional work, not a W fit.
Stops at first complete production candidates boundary, before admission,
proof queries or separate post-generation rejection. All generation-internal
filters remain. Public preflight/kindlaws/guards/sampling/cubes/family are included.

## Fields and remaining freeze prerequisite

`GENERATION_ROW.wallMs` and `.stageWalls.admissionPrefixMs` are the row's own
outer monotonic wall, excluding imports/model construction/output writing.
`stageWalls.substageWallMs` is null: no fabricated per-stage wall. For finer
sampling/cubes/filter/assembly splits D must freeze parent-observer hooks on
this exact source; do not reinterpret counted cprof values as milliseconds.
Output files: family.json, machine.json, identity.json, receipt.json.
Fields include count49, ordered raw+alpha family hashes, candidateNames,
proofQueries0, raw26-vector, exact source/flags/work and acceptance booleans.

No same-pin whole49hash exists yet. Historical quotient measurement43 and
A's older reference fixture are NOT that hash. After D explicitly permits
identity capture, replace `--expect /data/generation-identity.json` with
`--capture` (same rest of command). This emits `benchmarkAccepted:false`.
Freeze emitted identity.json bytes/SHA as /data/generation-identity.json,
then the command above checks them and accepts an anchored row.
Raw hash is SHA256(JSON.stringify(laws)) in original order; alpha hash is
SHA256(JSON.stringify(laws.map(strategyLawKey))). This is not A's additional
algebraic-normalization algorithm. Compare raw family bytes across pins,
not just same-count or differently defined hashes.

A's separate measurement-only commit595d5c74 provides same3bc GEN/REJECTION
boundaries and standalone13-law BASIS from post-rejection47. It is NOT the
uncommitted joint-SCC scheduler. Use one named GEN row, not both costs, and
assert compatible family identities before joining different-source rows.
No stage/anchor job is authorized until D freezes the kit and this manifest.
