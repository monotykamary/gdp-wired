# Isolated v3 validation

One authorized run: 2 CPU / 4096 MiB / requested 60 s / source-derived native 30 s.
The unchanged v2 ceilings are split into bootstrap 3 s + fresh load 1 s, then probe
2 s, broken 4 s, good 13 s, certificates 3 s = 26 s; clipped to the same 27 s finish
target. No real-time guarantee is asserted. Search remains 500 ms, and all nine
laws, the negative control, and strict acceptance are unchanged.

## Fix and isolation

`run.ts` and `bootstrap.ts` have only `node:` builtin imports, no imported helper,
checker, TypeScript import, dynamic import, or require. Preflight syntax/import
scans assert this without loading model/checker code. The bootstrap verifies the
same lock-integrity-bound TypeScript archive and all frozen inputs, copies pinned
source bytes into an exclusively created random private stage, then unpacks the
archive into that stage's new node_modules. It never touches repository/shared
node_modules or links source files to the shared tree.

After bootstrap exits successfully, the parent launches `load.ts` in a fresh
process at the private stage. This process imports TypeScript, the extractor and
checker and verifies TypeScript resolved to the private staged package. Only
then do unchanged model/control checks run. All commands use `bun --no-install`.
No network install occurs. The stage is removed by its creating parent after
outcomes have been retained; existing or shared node_modules are never removed.

## Evidence

Bootstrap writes synchronously flushed verification, copying and unpack boundary
markers. The fresh importer writes load completion. The parent streams those
markers to retained stdout as they arrive, even before the child exits. Phase
start/result records and exact compressed child stdout/stderr remain separately
retained and hashed. Parent output stays below 300,000 bytes (agent cap 400,000).
The probe and broken control still precede the positive check; partial certificate
files are examined even when that check fails. No partial outcome is all-nine
acceptance.

The old v1/v2 inputs, reports and native receipts are checked unchanged. No other
job is authorized by this plan, and no shared provider code, lifecycle experiment,
or requested limit increase is involved.
