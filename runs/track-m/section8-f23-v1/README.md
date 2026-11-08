# T-F2/F3 — sliced checking and identity-keyed caches

Research-only disposable snapshot on bx_3kjzmmhv, exclusive, eight pinned vCPUs.
The kernel and final harness check are unchanged. F2 slices each leaf to its
actually used hypotheses and exactly reindexes the certificate before checking.
F3 memoizes successful independent checks and retargets by immutable object
identity, goals, and the complete ordered scope key.

| Inv* metric | Control | Sliced/cached |
|---|---:|---:|
| Overall diagnostic wall | 35.017 s | 25.262 s |
| Exclusive kernel bucket | 10.003 s | 3.037 s |
| Counted units | 5161.6736204 | 5161.5263752 |
| Full-goal leaf checks / wall | 118 / 6.297 s | 0 |
| Sliced leaf checks / wall | 0 | 122 / 0.005819 s |
| Independent cut rechecks / wall | 1190 / 2.331 s | 460 / 0.938 s |
| Retarget rechecks / wall | 515 / 0.815 s | 631 / 1.844 s |

The kernel ceiling of 2.5 s is **not met**. Counted work changes by -0.1472452
units (-0.002853%), inside the requested 0.01% tolerance. All five verdicts
match; the other four counted totals match exactly. This is not exact
trace equivalence: the number and shape of admitted/transported leaf checks differ.

The sliced-check cache hits 32 times. Independent checking hits 1012 times.
The requested identity-keyed retarget cache hits **zero** times. Across sliced
checks, 59740 original hypotheses become 259 selected hypotheses (1–3 per
actual kernel call). This explains the large leaf-check win without claiming
that retarget caching solved the remaining cost.

Three sliced-check/cache tests pass. TypeScript and type-aware lint pass on
the instrumented candidate. No source or strategy implementation was promoted.
Raw and decoded receipts and per-law metrics are in this directory.
