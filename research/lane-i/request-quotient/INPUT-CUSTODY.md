# Recovered original input custody

This supplies the original bundles requested in D's
`lane-i-bfe647cf-source-audit/MAIN-DECISION.md`. No historical producer,
proof, timing or census computation was repeated. Existing `/tmp` input
directories survived and were copied unchanged into this worktree:

`runs/lane-i/quotient-input-custody/bundles/{census,q1,types}/`

These complete binary input bundles are retained on disk for D, not added to
Git. The full bundle-file hash manifest and every effective archive difference
are in `results/input-custody/quotient-retained-input-custody.log` (one long JSON
receipt line). `audit-input-custody.ts` reproduces the read-only audit on boat.

| Original scope | Exact source.tar SHA-256 | Effective files |
| --- | --- | ---: |
| Census / 9950X timing | `7d4506ba760d1811d7bedb4de4790fe1f03ad3508688e5fdad85f16d500314e0` | 5,809 |
| Q1 | `2433d63bf17311bf4dfa0f52fd405da99aa0e64303ebc813d873917986c020e6` | 6,042 |
| Final types | `99d1317bff409a11191872926a4dfb03e8fcdb65099d7800c8c52ad9382a96a9` | 6,097 |

The original final-types `verify.ts` is present unchanged, SHA-256
`b17b21a86e362558430c6cbf23773ce28fb26ca011a8f99d79715f2bdfa8fe55`.
It is not substituted with either older parent driver.

Boat batch `20261111-071022-6x4jrd`: native audit exit 0, 3.91 s.
Every effective extracted path is hashed (last tar member wins). Relative to
the census bundle, Q1 changes 233 paths and final-types changes 288 paths.
**All changes are confined to `research/lane-i/request-quotient/`; no runtime
file differs.** The complete path-by-path before/after hashes are retained.
These research/test/evidence overlays explain the differing input tar hashes;
post-extraction sampler hooks do not and are not offered as that explanation.

This closes the identified archive/wrapper custody gaps if D accepts the
independent comparison. It does not classify the old Q1 exceptions. The new
strict refusal audit is separate. New integration gates must still bind their
own exact inputs; historical W/timing claims do not transfer.
