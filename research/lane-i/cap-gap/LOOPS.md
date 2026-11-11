# I6 cap crossing and untrusted checkpoints

Baseline runtime: `1066f267`, unchanged in pre-repair `48cd625c` production.
The original thirteen old-profile overruns remain in `../hard-cap/LOOPS.md`.
This follow-up concerns the I6 `sharded_kv` crossing.

## Measured interval

The uninstrumented run uses **15,120,328.2561** units. The probe preserves
its exact raw vector and returned result, with 47,023 endpoint reads.
The root starts after 13 setup units; its absolute end is 15,000,013.
Relative to that start, the crossing interval is 14,965,848.2817 to
15,120,328.2561: **154,479.9744 units between polls**.

| Counter | Delta | Weighted units |
| --- | ---: | ---: |
| tableCells | 151,706 | 151,706 |
| fm | 79 | 184.07 |
| fcells | 308 | 3.7884 |
| plainRows | 164 | 1,300.52 |
| goalNodes | 2,613 | 1,285.596 |

The interval crosses row construction at `kernel/prove.ts:596` (`rowsAt` ->
`proverRows` -> `leafConstraintsReusing`) and open-atom discovery at line 606
(`openAt`). Hot sites include `kernel/kernel.ts:431` (`leafRows`), its cell-pair
loop, `decide` at line 67, and canonical-table/key parsing. No interpreter
evaluation counter increases. An evaluation-only sampler would miss it.
Evidence: `runs/lane-i/cap-gap-probe/`, `cap-gap-raw-analysis/`, `cap-gap-table/`.
Instrumentation changes only extracted temporary trees, not production.
These traces attribute work; they are not wall-time benchmarks.

## Repair

Four global-only checks in untrusted `kernel/prove.ts`: `openE`, `openC`,
`openH`, and the open-cell pair loop. In active full-work budgets,
`kernel/prover-rows.ts` delegates cache misses to `core/prover-row-budget.ts`.
Other modes retain the original builder, sharing and cache keys.

The new untrusted proposer uses the same public pure primitives and row order,
with polls between hypotheses, disjunctions, key coefficients, cells/pairs,
term expansions and appended rows. The checker still rebuilds its own rows
using the untouched reference implementation. Completed rows are observed
when appended; cancellation cannot skip their charges or cache a partial row
result. Tests retry after cancellation and compare with the reference.

No changes to `kernel/kernel.ts`, `core/check.ts`, Lean, raw observer functions,
weight/schema definitions or admission arithmetic. No raw-counter callback.
The two changed existing kernel-directory files are untrusted prover files,
not the trusted checker.

Pilot `884cbcd1`: 15,000,007.2817 units, unknown `work budget (row cell pair)`,
exact flags-off vector/result; 20 tests / 793 assertions pass. Append-time
observation follows at `9c9ea506`, with test-only follow-up `c4359d8b`.
Final source `17119b50` adds explicit full-profile guards. The independent
audit passes: sharded_kv 15,000,018.2817; corpus maximum 15,000,276.18.
See `RESULT.md` and `AUDIT.json`.

Acceptance slack: **1,024 provisional raw-work-v1 units**, to be rechecked
on repricing. This finite census is not an instruction-level proof for
arbitrary-size unchecked inputs or still-unported B/F closing-check paths.
