## Current directive — finish accounting and ledger without waiting on D1

Coordinator is auditing `c9eb0f9c` in parallel. Continue all remaining I2
accounting, then the phase ledger and all-29 repeat/cross-CPU determinism
census, one job per VM. Commit each verified piece; do not pause at the
kernel-audit boundary. No calibrated weights or W have been selected here.

## For lane A

Original failing source: `8901715e39a384583b22a5ea2856d93f795807fd`, gate base
`b11e1f65`, boat batch `20261110-105202-wd6w0o`, job `clock-shard-5`.

1. `core/cli.test.ts:480` — **flows, leases and effects: at most one call
   between, keys that expire, a charge made once** (test starts at line 453).
   The no-expiry acquire/release check returned `unknown`, expected `proven`.
   Call: `check([lockPath], {ms: 8000, propose: false, env: 'acquire then release'})`.
2. `core/cli.test.ts:1122` — **the CLI on supercomputer's shapes: aliases,
   shadowing, guarded products, floor division, integer sums, scoping, Houdini**
   (test starts at line 991). The reachable `Pending` integer-map sum returned
   `unknown`, expected `['proven']`.
   Call: `check([sPath], {ms: 8000, propose: false, from: 'reachable', entry: 'Pending'})`.

**Seed provenance:** neither original check call sets a seed, and the saved
job manifest supplies no seed or `FUZZ_SEED` override. A numeric run seed / the
inherited seed environment is **not recorded in the original receipt**; do
not invent one or label this a seeded protocol-census run. Preserve that gap
when handing it over. Manifest:
`../gdp-wired-trackK/runs/t20-clock-suite-jobs.json`.

**Exact retained log:**
`../gdp-wired-trackK/runs/t20-clock-suite/clock-shard-5.log`.
Its shard stream is 143,078 bytes, SHA-256
`525a80c716b5830715073925b49452b4a5dd56395bd8e14e8f0e8b2e2939503a`.
Receipt: `../gdp-wired-trackK/research/track-gen/t20-suite-first-result.json`.
Full-context command was `bun scripts/test-shards.ts --shard 5/8`; original
job timeout 900 s, 4 CPUs / 14,336 MiB. Do not replace it with an isolated retry
or increase either 8,000 ms search allowance.

Original result remains **273 passes / 2 failures** in that shard, with
1,632 passes across the first full-suite attempt. Later isolated controls
and full shard-5 context checks passed according to lane A's
`t20-validation-progress.json` (recheck `20261110-111313-7tv8x3`, audit
`20261110-111906-5w41pe`): 1,708 combined passes, **not a single clean original
suite run**. Those later receipts do not erase the failures or establish a
numeric seed for the original run.
