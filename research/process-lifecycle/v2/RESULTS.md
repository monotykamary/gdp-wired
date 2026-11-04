# Instrumented lifecycle v2 — retained setup failure

## Actual execution

Exactly one distinct instrumented job was launched. No duplicate or follow-up run
was made.

| Field | Retained value |
|---|---|
| Batch | `20261104-111929-p60u1y` |
| Uploaded tree | `d800dcb13354` (2013 files) |
| Image | `sc-f0d8daeee6c3` |
| Manifest SHA256 | `9f1caab4b9d7cb7224ff8d93726e645fb2e01cb0b5e90bdad98335037df87902` |
| Requested | 2 CPU / 4096 MiB / 60 s |
| Native source-derived limit | 30 s |
| Worker result | **exit 2, 0.65 s** |
| Controller result | exit 0 (delivery completed, **not validation success**) |
| Placement | `bx_85wyqdj5`, large, 2 allocated / 8 host vCPUs, nonexclusive |
| Fallbacks / charged starts | none / zero |

These metadata do not attest the exact worker binary or establish a real-time
guarantee. The native limit remains source-derived, as in the prior diagnosis.

## Retained phase evidence

The parent wrote five contiguous synchronous stdout records. All decode correctly,
with the exact frozen manifest hash and verified decompressed output hashes:

| Sequence | Event | Outcome |
|---|---|---|
| 0 | Start, 0 ms | Runtime reports Bun 1.4.3, Node compatibility 26.3.0 |
| 1 | Manifest, 4 ms | Hash matches frozen input manifest |
| 2 | Setup start, 4 ms | 4000 ms child ceiling |
| 3 | Setup result, 454 ms | Child exit 1, 424 ms; no signal or spawn error |
| 4 | Fatal, 457 ms | `pinned setup failed; no model checks attempted` |

Setup stderr is exactly:

```text
error: Cannot find package 'typescript' from '/work/gdp-wired/research/process-lifecycle/v2/phase.ts'

Bun v1.4.3 (Linux x64)
```

This is **not** an exhausted resource budget or another 30-second timeout. The
setup entrypoint contains a literal `import('typescript')` in the same module that
is meant to unpack the package before loading it. The observed loader refusal is
consistent with that bootstrap dependency being resolved before it is available.
There are no internal setup markers proving whether archive verification or
unpacking was reached; no stronger execution-order claim is made.

The locally downloaded archive was SHA512-verified against the existing lockfile
before launch. That preflight integrity fact does **not** show the remote setup
completed. A future correction would separate a builtins-only bootstrap from the
module that imports TypeScript and retain markers around each boundary. No such
corrected validation has been launched or claimed here; this run's files remain
frozen.

## Acceptance status

- Setup: **failed**.
- Finite pure probe: **not started**.
- Broken-control CLI/replay: **not started**.
- Nine-law positive CLI: **not started**.
- Certificate replay: **not started**.
- Retained certificates: **zero**.
- Validated laws claimed: **zero**.
- All-nine-plus-negative-control acceptance: **not obtained**.

The earlier original timeout packet remains unchanged. All 230 v2 input hashes
and original receipt-bound file hashes were checked again after this attempt.
The instrumentation preserved the completed setup outcome and its stderr despite
the later fatal result. That narrow observation does not establish every failure
mode or deadline property of the runner.

## Evidence paths

Under `runs/astra-mac-lifecycle-v2/`:

- `controller.log`, `results/{summary.tsv,placement.json,backends.json}`
- `results/pure-lifecycle-instrumented-v2.log`: raw five-record stream
- `decoded/events.json`, `decoded/setup.{stdout,stderr}`
- `bundle/input-manifest.json`, `freeze-receipt.json`
- `retained-report.json`: artifact decoder output; does not rerun proofs/kernels
- `native-receipt.json`: batch/tree/outcome and retained file hashes

No shared scheduler/provider code changed, no real lifecycle signaling experiment
occurred, and historical `research/egraph` files were not changed. No retry is
covered by the now-consumed single-run authorization.
