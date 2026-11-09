# Bounded per-op diagnostic and entry profile

Research only. Engine **5974b9165d6860f1157f3bed3cd66a7e1514e904**. Production, kernel, strategy, budgets and the 1,500-unit row ceiling are unchanged.

## What was run

The deadline-free batch was stopped/censored; see [the retained receipt](../section12-censored-v1/README.md). Its Inv* process hit the external one-hour watchdog while still in op 3 (exit 137, 3,602.85 s). Only completed op 0–2 spans have counted receipts: **582.893924 units**. The in-flight op 3 counter is unavailable. The earlier live observation was 1,425.56 s / 6,562,328 kB RSS, not a terminal measurement.

Replacement batch `20261109-064438-b0or32` ran eleven independent captured-entry shards. Each had a **50,000 counted-unit** research stop and **600 s** wall watchdog. All ended normally before the watchdog. A single atomic counter update can overshoot the unit stop; actual spent units are reported below.

Each job was alone on a **large, eight-pinned-vCPU AMD Ryzen 9 9950X VM**. The scheduler supplied **eight VMs**, not eleven distinct simultaneous VMs; three were reused after their previous shard finished. Actual assignments are in [placement.json](../section13-shards-v1/placement.json). No scheduler policy was changed. All shards reused the same prepared, checksum-verified runtime bundle on image `sc-f0d8daeee6c3`; there was no per-shard dependency install.

The research override disables **local deadlines too**, not just the law's total allowance. These are therefore **not** measurements of the ordinary production procedure with only a larger budget. The entry profile below demonstrates the difference.

## Per-op results

Wall is the measured search/check interval, excluding archive serialization. SAT/refuted are **raw source-query results**; raw refutations are not necessarily admitted checked cuts. Checked/reused/unknown admission outcomes are separate fields in [summary.json](summary.json).

| Law | op | Result | Counted units | Wall s | Terminal leaves | Cuts | Source SAT / raw refuted |
|---|---:|---|---:|---:|---:|---:|---:|
| Inv* | 3 | unknown | 50,032.695596 | 49.813 | 0 | 0 | 0 / 0 |
| Inv* | 4 | unknown | 50,002.724416 | 168.956 | 4 | 23 | 32 / 29 |
| Inv* | 5 | unknown | 50,001.818791 | 364.528 | 41 | 46 | 99 / 102 |
| Inv* | 6 | unknown | 50,084.732049 | 48.118 | 0 | 0 | 0 / 0 |
| Inv2973 | 0 | unknown | 50,006.255684 | 103.358 | 3 | 37 | 50 / 36 |
| Inv2973 | 1 | unknown | 50,003.020969 | 146.372 | 2 | 24 | 48 / 23 |
| Inv2973 | 2 | unknown | 50,000.004158 | 155.667 | 2 | 41 | 33 / 40 |
| Inv2973 | 3 | unknown | 50,000.040548 | 52.740 | 0 | 0 | 0 / 0 |
| Inv2973 | 4 | **closed, checked** | 20,732.071099 | 510.549 | 9 | 130 | 237 / 174 |
| Inv2973 | 5 | unknown | 50,002.166392 | 229.309 | 3 | 58 | 78 / 158 |
| Inv2973 | 6 | unknown | 50,033.847734 | 47.583 | 0 | 0 | 0 / 0 |

**No complete law closed.** A checked op branch is not a complete-law proof. Inv*'s four shards spent 200,121.970851 units; Inv2973's seven spent 320,777.406584 units. These sums count independent work and must not be called the minimum cost of either law. The ordinary production allowance remains **5,000 per law**; in particular, op 4's 20,732-unit diagnostic result is not evidence that production needs that amount.

## First unfinished scopes and models

[summary.json](summary.json) preserves each first recorded failure's exact guard path, full numeric point where one exists, complete violated set, and every violated instance's source result and spent units. The live `Invstar-op<N>.json` / `Inv2973-op<N>.json` files additionally retain attempt details but are deliberately ignored by git. Their full original forms are in the archives.

- Inv* op 3/6 and Inv2973 op 3/6 hit the stop in closure preparation, **before any numeric leaf**. They have no numeric model or violated set. The initial `path: []` output was a reporting placeholder; it was corrected from the recorded active closure guards. It was not evidence of an unguarded action-entry search.
- Inv* op 4: first recorded `batch-exhausted` scope; validated point, **31** violated instances.
- Inv* op 5: cap during a numeric leaf before that query returned a model; no model is invented or borrowed from an earlier leaf.
- Inv2973 op 0/1: first recorded `batch-exhausted` scopes, **122 / 107** violated instances.
- Inv2973 op 2: first recorded `no-batch-core-or-model` scope, **66** violated instances.
- Inv2973 op 5: recorded point with **95** violated instances when work stopped.
- Inv2973 op 4 closed and has no failing scope.

An independent audit passed for all eleven records: non-double-counted ledgers, verdict consistency, exact integer evaluation of captured path inequalities and complete violated sets, source-index coverage, and source-unit sums. The production proposer had already validated each recorded numeric model before emitting it. This audit does not turn unknown into refuted, or a raw source refutation into a checked cut.

## Decisive Inv* op 3 entry profile

Requested file: [Invstar-op3-entry-profile.json](Invstar-op3-entry-profile.json). Two fresh processes on exclusive `bx_2eg9t59n` compared the normal five-law production prefix with the captured-entry deadline-free shard. Kernel bytes are identical; only untrusted call-boundary instrumentation was added.

| Measurement | Normal production | Deadline-free shard |
|---|---:|---:|
| op 3 counted units | 1,148.608413 | 50,032.659118 |
| op 3 wall s | 2.324 | 43.763 |
| first numeric leaf: op-local units | **701.150586** | **not reached** |
| activation nodes before first leaf/stop | 9 | 9 |
| activation cases before first leaf/stop | 4 (3 inactive, 1 active) | 4 (3 inactive, 1 active) |
| row cases before first leaf/stop | 1 | 0 |
| grow query calls / counted units | 13 / 211.584108 | 8 / 49,235.932682 |
| model/core query calls / counted units | 143 / 935.864300 | 52 / 796.270124 |
| legacy selection calls / inclusive units | 7 / 41.837288 | 1 / 11.008834 |
| closure calls / inclusive units | 2 / 614.541153 | 1 / 49,914.259228 |
| natural-case query calls / units | 1 / 0 | 0 / 0 |

**Cause: one nested `grow`, not case enumeration.** The interrupted 235-hypothesis query alone consumed **49,100.134260 units / 41.360 s**. The stack is activation case → field-bound lemmas → derivability closure → field-source fallback with `closure:false` → `grow`.

`core/count-recovery/derivability-closure.ts:98–100` normally grants that field-source attempt at most 250 units. `withoutDeadlines` freezes both `clock()` and `performance.now()` at zero, so that local ceiling and inner deadlines never expire. Normal production can abandon this preparation and reach the 31.86-unit numeric leaf. The shard cannot do so before its external 50,000-unit stop. **The shard outcome does not establish a 50,000-unit lower bound on production need.**

The profile file gives counted units and real wall by function and query kind, with both inclusive and exclusive columns. Inclusive scopes nest and must not be summed. It also includes the interrupted goal/path packet for short, bounded follow-up experiments. The first profile attempt lost its output to a nested-directory archive error; it is recorded as an artifact failure, not a numerical result. The writer was fixed, regression-tested, and only that profile was repeated.

## Artifacts and workflow

- [Audited compact summary](summary.json) and [entry profile](Invstar-op3-entry-profile.json) are committed. No `columns` dump or giant per-op JSON is committed.
- Full original receipts: `../section13-shards-v1/<job>/receipts.br`, each with `archive-manifest.json` and SHA-256. Expanded duplicate dumps were removed only after verifying these archives. Total compressed shard receipts are about 8.5 MiB.
- Prepared-runtime and unchanged-source receipts: `../section13-runtime-v1/` and its preparation manifest. The source is pinned to 5974b916.
- Profile archive and integrity receipt: `../section13-entry-profile-v2/`.
- Audit receipt: `../section13-audit-v1/`; exact path/violated-set checks completed in 0.06 job seconds.
- Implementation: `9ccf0b97`. Final remote validation (`../section13-check-v4/`): typecheck/lint pass, **9 tests / 33 assertions pass**.
- Fast loop: use `research/track-m/replay-section13-leaf.ts` on one captured goal/path with a small counted budget; parallelize independent packets. Reserve three-repeat interleaved wall runs for gate checkpoints. No new wall gate is claimed here.
