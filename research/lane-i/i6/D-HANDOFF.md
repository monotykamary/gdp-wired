# I6 source review handoff — PENDING-D

- Base: `00b58ee54b4e5b8c4967fdbde35d1ff0f38d91e7` (your scoped gate `f95b8061`).
- Observation-only production patch: `3281eb7fdcda5e04aab2c67a4950ee8e36cf1ef0`.
- Clean static evidence source: `1066f26766d6bfd628c8ef9de92bc626357b01c1`; no production differences from `3281eb7f`.
- Minimal four-file delta: `counter-only.patch`, SHA-256 `68588903c28378e40257eb239f52f4a212b0afcafe55c8d73cac7f01764545f8`.

## Scope

Wire the three declared-but-unwritten raw columns at their actual work sites. Table construction/canonical-table scans and cache accesses write `tableCells`; visited certificate/tree/derivation nodes write `checkSteps`; sampled forms/cubes and direction/residual tests write `cubeTests`. Reads served by existing caches do not charge the work skipped by the cache.

The pure helpers in `core/meter.ts` do not call search, clock, budget, or any callback; they cannot accept a proof or change a checker branch. They are off when GDP_WORK_FULL is off. Only `kernel/kernel.ts` and `core/check.ts` change among admitted identities. The patch does not import A's prover, alter a checking rule, modify Lean, or add a price. The current provisional prices are not a fit for these newly visible counts.

## Verified on boat

- 121 tests / 1,356 assertions; real-site count tests and existing cap controls pass.
- Typecheck/type-aware lint: 1,791 files, zero errors/warnings.
- Independent TypeScript AST erasure removes exactly five named observation helpers/imports and recovers the original checker, kernel and inference code.
- 132 other protected identities and prover body exact.
- Failed static attempts were harness-only typing errors and are retained in evidence.

## Still open; not claimed

The 28-original strict / flags-off census is complete: 10 proved/checked, 18 unknown; all flags-off receipts remain exact. `simple_election` and `client_server_ae` changed budgeted verdicts; completed same-source writer-on/off, lifted-global-cap and shadow-writer controls identify an accounting-driven local/outer stop, not a persistent proof failure (`CAUSAL.md`). Both cases prove with writers on at 1e12, and shadow exactly matches off in the old 23 counters and normalized results. `sharded_kv` reaches 15,120,328.2561 units, exceeding the old 1,024 slack. This is an observation-gated source, not an accepted no-loss/hard-cap result. Exact equal-work raw-vector and Inv*/K3 tail wall/units runs now use B's committed capture `cace38bc`, with saved term-column rebinding and packet hashes. The final integrated cap and calibrated W are not established by the focused tests. Any budget-driven earlier stopping must be reported rather than excluded from the audit. Separate A/B/F gates do not constitute a composition gate.

B9 confirms native STEP checks at zero legacy units (first star 12.28s, row 3.47s). These are reference timings, not measured I6 results. B is exporting the exact checker inputs so the dominant tail can be replayed on this admitted-base line without importing ungated strategy code.
