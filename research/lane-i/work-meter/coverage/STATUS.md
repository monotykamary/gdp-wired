# Coverage checkpoint

Verified source chain (separate branches; not merged into the integration gate):

| Stage | Commit | Parent | Validation |
|---|---|---|---|
| Raw observations | `9a36137e` | original `b11e1f65` | source identity, selected tests, erasure, mutation controls, type/lint |
| Phase ledger | `feeaccf2` | `9a36137e` | 151 selected tests, erasure, roster, decoder, type/lint |
| Boundary scopes | `4550377f` | `feeaccf2` | 151 selected tests plus the same checks |
| Bitmap word observations | `84ffacf2` | `4550377f` | 155 selected tests plus the same checks |
| Canonical key observations | `41d39043` | `84ffacf2` | 158 selected tests, erasure, type/lint, three 267-test mutation suites |
| Request allocation observations | `94b65671` | `41d39043` | 164 selected tests, erasure, type/lint, audited reuse of three 267-test mutation suites on identical production blobs |

Boundary/bitmap source transport hashes were verified against the exact tested
source in `20261110-202611-ljsgom`. Zero/double/random mutation controls of the
full bitmap composition passed there too. Source trees respectively:
`efff50dddfb3d66c40e83c2c8c6da78cc067d14d` and
`26677094653194059ef55e17db54ca7e7c17cf2d`.
All retain original model blob `0541fa9436e307a6fb716aa5064637b30b893b79`.

## Canonicalization — verified source, limited diagnostic claim

Original-model Node pilot `20261110-202238-v6auwd` retained identical raw counts
and verdict with its observer off/on. It reported ~300ms quiet windows with
recent stacks in `canon`/`canonFlip` -> `decide` -> `sameKey` -> `leafRows`.
These are candidates, not final F3 proof: the first observer did not recheck
its heartbeat after the profiler's asynchronous acknowledgement.

`canonicalization.ts` stages only discarded additive observations on the
existing lookup, string-key serialization/inspection and key parsing paths.
It does not change sort order, cache rules, formulas, acceptance branches,
weights or W. The required structural checker-erasure audit remains enabled.
New exact-observation tests exercise cold and cached canonicalization.
The source checks and original-model Node pilot passed in
`20261110-203555-pkp0td`; zero/double/random controls passed in
`20261110-204037-4iirg6`. The stricter Node sampler preserved exact raw counts
and verdict, and classified nine windows as changed during capture, with
zero stable violations. This is not a weighted F3 or overhead qualification.
Independent source-transport, receipt and phase-reconciliation audits passed
in `20261110-204538-t42ntt`. The exact source is frozen as `41d39043` on
`claude/lane-i-complete-canonical`; see `VERIFIED-SOURCE.md`.

## Fenced follow-up on the frozen canonical source

`20261110-211555-pdxwgb` again preserves the off/on raw vector, verdict and
source blobs, but its strict capture audit finds three stable windows and
11 changed windows. Two stable samples are GC; one is application work in
`instance` / `dataFilter`. The same-source bundle reconstruction
`20261110-213128-eh7sxk` matches the line and named-function anchors to
`core/infer.ts`'s Cartesian request-product materialization, before its
`combosMax` truncation. No additional solver run was used for that mapping.

Those request allocations now have discarded observations in the separately
verified source `94b65671`. Exact controls retain order, overwrite behavior,
map identity, truncation and RNG calls. The source/receipt audit and exact
parent-tree export pass; see `../requests/VERIFIED-SOURCE.md`. New-source
observation is still pending. GC samples are retained, not exempted.

No claim of complete coverage, Bun F3, F4 census, calibrated weights, or W.
