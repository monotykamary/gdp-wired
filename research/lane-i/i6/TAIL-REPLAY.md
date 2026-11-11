# I6: exact B9 native closing-check replay

## Custody and source

B producer `cace38bc`, capture base `826b2dd1`, packets from `research/track-m/final-check-inputs/manifest.json`. Each decompressed SHA-256 is checked before execution. All saved process-local term-column expressions are rebound through the selected kernel's own `termColumn`; captured numeric IDs are not treated as authority. No B strategy/helper module is imported.

Baseline **`3d0256f0ee6a578ad005b9169c4cff3cd2eaf602`** (admission optimization, before I6); candidate **`1066f26766d6bfd628c8ef9de92bc626357b01c1`**. Both have the same algorithms, as independently checked by I6 AST erasure. `GDP_WORK_FULL=1`, existing positive provisional prices unchanged. No search budget is installed: these are completed native check measurements, **not admission-policy or original-family acceptance receipts**.

Batch `20261111-043520-1uykdc`, one VM per target, no co-tenants, two fresh processes per source in ABBA order. Host boot IDs and loaded checker hashes are recorded in every process. Actual affinity: six pinned vCPUs.

## Results

All 16 original native calls accepted. All 16 matching empty-derivation mutants were rejected. Packet hash and all other 23 raw columns are identical across sources. All 26 baseline columns are zero during these calls.

| Target / phase | `tableCells` | `checkSteps` | New total units | Baseline wall ms (two samples) | I6 wall ms (two samples) |
|---|---:|---:|---:|---|---|
| Inv* STEP | 79,054,329 | 7,622 | 79,061,951 | 18,099.118 / 17,235.635 | 17,327.925 / 18,355.760 |
| Inv* INIT | 1,109 | 17 | 1,126 | 2.152 / 0.684 | 1.846 / 0.740 |
| K3 STEP | 77,938,079 | 13,140 | 77,951,219 | 13,741.668 / 5,168.100 | 12,533.836 / 14,549.784 |
| K3 INIT | 56 | 4 | 60 | 0.513 / 0.154 | 0.610 / 0.393 |

Inv* host: AMD EPYC 4585PX; K3 host: AMD Ryzen 9 9950X. `cubeTests` is zero in these native final checks, as expected; the counter is exercised in inference rather than here. Exact raw vectors are in the paired receipts. The large K3 baseline spread prevents a defensible observer-overhead ratio from two samples; no speedup/slowdown or reference-host fit is claimed.

## Evidence and limitations

- `results/tail/`: successful paired logs, placement and summary.
- `results/tail-initial/`: initial consumer failure retained. Producer `bytes` is JavaScript string length, not UTF-8 byte length (e.g. Inv* STEP 676,798 code units / 677,050 bytes). The corrected consumer checks that exact code-unit field, records actual UTF-8 bytes, and retains the stronger exact-byte SHA-256 check. No packet content was changed.
- Kernel/arithmetic baseline SHA-256: `d939a673cd1187a0406a0ad4ea4354593537192d52035e5713228ab4764e12bc` / `9ae2d3c4323dd1e22d02219c1f33dcd92dfc6856a7500e969b43232d2fa6fd5b`.
- I6 kernel SHA-256: `1e2c9770632f3aeeadd36ea09f3f90cf169b06948abdeaf88bf0150a50d3f240`.

This verifies that formerly unobserved native checking now writes positive raw work and preserves the replay verdicts and other counters. It does not approve the B strategy dependency graph, remove a closing check, prove an original MLDR family, or establish the 15M hard cap or fitted W. The unit totals use provisional weight 1 for the new columns; they are not elapsed milliseconds.
