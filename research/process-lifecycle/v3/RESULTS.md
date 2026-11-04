# Isolated v3 — bootstrap fixed, strict validation not accepted

## Actual job and provenance

One authorized run, no retry. Batch **`20261104-112330-7v7woj`**, uploaded tree
**`c9841b112893`** (2020 files), image `sc-f0d8daeee6c3`. Worker **exit 2 / 3.53 s**;
controller exit 0 means collection completed, not validation success. Requested
2 CPU / 4096 MiB / 60 s; source-derived native limit 30 s. The 26 s child ceilings
and 27 s finish target were unchanged. None of these observations is a real-time
guarantee or exact historical native-spec/worker-binary attestation.

Manifest: `2bb44d45ebbe96c525fddf7ff132bb580b9f7a9b010e11a183265da913b1c708`.
All **236** frozen source/input hashes and the v1/v2 receipt-bound files still
match. Placement was `bx_85wyqdj5`, large, 2 allocated vCPUs on an 8-vCPU host,
nonexclusive, recorded zero co-tenants. No fallback or charged start was recorded.

## What actually completed

| Phase | Exit | Observed duration | Result |
|---|---:|---:|---|
| Builtins-only bootstrap | 0 | 175 ms | Verified inputs/archive; copied and unpacked private stage |
| Fresh importer | 0 | 205 ms | TypeScript 5.9.3, extractor and checker loaded; private resolution verified |
| Unchanged finite probe | 0 | 57 ms | 15,625 sequences / 93,750 transitions; concrete broken-drain replay passed |
| Broken-control CLI | 1 | 883 ms | Reported broken with a four-call trace |
| Nine-law positive CLI | 0 | 2,128 ms | All nine reported proven; nine certificate files produced |
| Certificate collector/replay phase | 2 | 33 ms | Source-location predicate rejected every file **before kernel replay** |

There are **23 contiguous retained parent records**, including streamed internal
verification, copy, unpack and load boundaries. Verification completed at parent
31 ms, private unpack at 174 ms, fresh load at 379 ms. This closes the observed v2
bootstrap failure for this run. It does not prove a general deadline property.

The positive extraction report records 2074 requests from the start, 400 from drawn
states, 18 from prover witnesses, and 15/15 branch arms. The negative report records
2074/400/10 and 10/10 arms. These are producer-reported finite cross-checks, not an
unbounded proof of the source-to-model relationship.

## Why overall acceptance remains false

Two assumptions in my frozen collector contract do not match the retained output:

1. **Source location representation.** The collector expected
   `research/process-lifecycle/model.py:12`, while the document contains
   `meta.file = research/process-lifecycle/model.py` and `meta.where = model.py:12`.
   The same basename-versus-full-path mismatch occurs for all nine documents.
   Static inspection confirms their other source metadata and basename/line pairs
   match the unchanged annotations. It does **not** run the kernel or override
   the frozen predicate. Because the predicate precedes `checkDocument`, none of
   the nine documents reached that independent replay in this attempt. This is
   not a kernel rejection of their proof contents.
2. **Negative replay field.** The frozen final predicate requires a truthy
   `law.replayed`; the negative CLI JSON contains `verdict: broken` and `run`, but
   no `replayed` property. Therefore the predicate remains false independently of
   the certificate issue. The CLI source emits that field only conditionally;
   no new explanation of its absence is asserted. We do not replace the missing
   field with an inference from the separate finite probe.

The negative CLI trace is `step(0), step(-1), step(1), step(2)`. The unchanged
finite probe separately replays `step(0), step(1), step(2)`, ending at `phase=2`,
`inflight=1`. These are distinct pieces of retained evidence, not interchangeable
receipts for replaying the exact CLI trace.

Thus **nine producer-reported proven laws and nine retained documents are partial
positive evidence, not all-nine-plus-negative-control acceptance**. No additional
prover run, source trace replay, or independent certificate kernel execution was
performed while decoding/inspecting the saved packet. Acceptance was not weakened
or retroactively changed.

## Retention and boundaries

Under `runs/astra-mac-lifecycle-v3/`:

- `controller.log`, `results/`: actual worker output, summary, placement/backends.
- `bundle/input-manifest.json`, `freeze-receipt.json`: source/archive pins and
  builtins-only import scans.
- `decoded/events.json`, `decoded/{bootstrap,load,probe,broken,good,certificates}.{stdout,stderr}`:
  exact decompressed subprocess evidence; every compressed payload hash checked.
- `decoded/Lifecycle.*.json`: **all nine exact certificate bytes**, individually
  SHA256-bound in `retained-report.json` and `native-receipt.json`.
- `metadata-inspection.json`: non-executing location/field comparison only.

The source-derived platform premise remains conditional. No supervisor, OS signal
experiment, shared provider change, shared node_modules mutation, or historical
egraph change occurred. Cyclic diagnostics in this producer log are not a new
historical egraph/M2 acceptance claim. The v1/v2 packets remain untouched; the one
v3 authorization is consumed. Any subsequent execution needs a new scope and must
preserve this failed strict verdict.
