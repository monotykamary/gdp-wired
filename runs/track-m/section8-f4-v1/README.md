# T-F4 — rejected incremental-row prototype

Measurement-only on bx_3kjzmmhv, exclusive with eight pinned vCPUs. The
prototype caches each hypothesis' facts and recorded decision dependencies;
children recompute only affected hypotheses. The ordinary row assembler is
copied verbatim into untrusted research code, not changed in the kernel.
The existing 4096-entry ceiling and a 250000-hypothesis-reference retention
limit bound the cache. All final checks remain unchanged.

## Result: drop F4

| Inv2973 metric | Control | Incremental |
|---|---:|---:|
| Exclusive remaining-phase row materialization | 8.551 s | 22.997 s |
| Inclusive rowsAt wall (overlapping other phases) | 29.045 s | 48.635 s |
| rowsAt calls | 13364 | 12094 |
| Complete diagnostic wall | 48.186 s | 60.800 s |
| Counted units | 5002.6530104 | 4883.592478 |
| Checked | false | false |

The <=2 s prediction fails, and there is no 50% saving. The candidate hits the
unchanged 60-second wall before the counted limit, so the work is not identical
and these numbers are not a matched-trace speed ratio. The observed increased
cost despite less completed work is enough to reject this prototype.

Across the candidate process, 14033332 hypothesis blocks were reused,
421944 recomputed, and 82413 child states constructed; caches cleared 33 times.
Avoiding fact recomputation alone did not make complete row materialization
cheap. This profile does not isolate the exact copying/assembly subcost.
All five verdicts agree; the three proved laws' counted totals match exactly.

## Validation

Both real snapshot differential tests pass, checking 20 sibling/nested paths
against the unchanged kernel builder, including row aliases and duplicates.
The initial completed profile ended with two unused-import lint errors; removing
only those imports does not change the measured algorithm. Final validation in
`../section8-final-validation-v1/validate.log` passes TypeScript and type-aware
lint for the plain tree and the F4 snapshot: 10 tests / 46 assertions on the plain
tree, then the two differential tests / 20 assertions again on the snapshot.

No production source, default, cap, allowance, or trusted rule was changed.
The Section 8 implementation pass line fails; no new Gate 1 run is authorized
by these results. Raw and decoded profiles and `results.json` are retained here.
