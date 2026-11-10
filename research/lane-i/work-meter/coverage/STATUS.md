# Coverage checkpoint

Verified source chain (separate branches; not merged into the integration gate):

| Stage | Commit | Parent | Validation |
|---|---|---|---|
| Raw observations | `9a36137e` | original `b11e1f65` | source identity, selected tests, erasure, mutation controls, type/lint |
| Phase ledger | `feeaccf2` | `9a36137e` | 151 selected tests, erasure, roster, decoder, type/lint |
| Boundary scopes | `4550377f` | `feeaccf2` | 151 selected tests plus the same checks |
| Bitmap word observations | `84ffacf2` | `4550377f` | 155 selected tests plus the same checks |

Boundary/bitmap source transport hashes were verified against the exact tested
source in `20261110-202611-ljsgom`. Zero/double/random mutation controls of the
full bitmap composition passed there too. Source trees respectively:
`efff50dddfb3d66c40e83c2c8c6da78cc067d14d` and
`26677094653194059ef55e17db54ca7e7c17cf2d`.
All retain original model blob `0541fa9436e307a6fb716aa5064637b30b893b79`.

## Follow-up: canonicalization, not yet validated

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
A stricter sampler records heartbeat-before/after and classifies changed
windows separately. Both the new composition checks and original-model
Node pilot are running via `canonical.jobs.json`.

No claim of complete coverage, Bun F3, F4 census, calibrated weights, or W.
