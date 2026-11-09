# T-11.5 — normal ceilings and root-cut tiering (research only)

Implementation: **`2e0007de`**.

**Result: the tested root-cut lift does not meet the prediction. No complete law or gate pass is claimed.** Production files, production allowances and the kernel are unchanged. The disposable proposer is frozen at `5974b916`; its three instrumentation-only file changes are listed in `../section14-prepare-v1/integrity.json`. All local ceilings run on ordinary clocks. The diagnostic total law allowance is **50,000**, versus **5,000** in production. A normal action/leaf may stop well before that total: the production allocator and stopping rules are deliberately intact.

## A. No-inflight-dump control

Inv2973 op 4 is **unknown**, **16,672.478177 units**, **29.018535 s**, one terminal leaf visit, 36 learned cuts, 21 source SAT results / 35 checked source refutations. It stops on `op=4, started=1, a$#=i, b$=i`, with a recorded model and 141 violated instances.

The former deadline-free run closed nine leaves at 20,732.071099 units / 510.549 s. **This is not a same-work wall comparison:** restoring local clocks changes the path and stopping point. The new wall cannot establish an I/O-only speedup. It does establish an honest no-dump, ordinary-clock control.

## B. What actually lifts to the root

The census reproduces **129 checked attempts, 79 distinct pool indices**. Section 11.5's listed categories are 34 frames/bridges plus **45**, not 51, non-frame candidates. Rather than invent six facts or assume the prose's classification, the probe tested every one of the 79 as an independent, unguarded counted goal. Each positive result passes `checkCounted`, then empty-guard conditional-cut admission.

| Category | Candidates | Independently checked | Source-query SAT |
|---|---:|---:|---:|
| Same-state inclusions | 11 | 6 | 5 |
| Three-term partitions | 20 | 20 | 0 |
| Five-term purported partitions | 8 | 0 | 8 |
| Ranges and purported self-zero | 6 | 5 | 1 |
| **Non-frame subtotal** | **45** | **31** | **14** |
| Frames / pre-post bridges | 34 | 0 | 34 |

The 31 proofs cost **2,326.806831 units**. All 79 trials, including SAT candidates, cost **3,110.262124 units / 25.052458 s**. New root goals have a 1,000-unit and 30-second cap each; this does not change an existing production local ceiling. The literal instance set includes post-state reads and five proved facts involving auxiliary counts outside the five named maps. Restricting the non-frame candidates literally to xm, xn, cfgSize, inS and inX gives 38 candidates, 26 proved. The seeded test generously uses all 31 proved facts. No claim is made that all 31 are generic, pre-state-only templates shareable across laws.

The 14 non-frame candidates that did not lift are indices **108, 110, 111, 112, 115, 185, 253, 254, 257, 258, 281, 282, 285, 286**. In particular, index 185 is `xm#[b$,a$#] <= 0`, not syntactically a self-zero at an equal key. Index 110 is `inS <= cfgSize[i]`. Their checked leaf proofs do not justify asserting them unguarded at the root. A SAT source query here is **not** an MLDR counterexample.

For completeness, all 48 unsuccessful candidates were also retried against the **full 1,341-hypothesis law-root goal**, without an op/leaf guard, using 1,000 units per goal. **Zero additional proofs**: all time out before a case split. This diagnostic costs **50,066.458559 units / 139.280292 s**, not a production requirement or a lower bound. The full-root probe includes the original negated target: it tests root consequences, not universally valid state identities.

## C. Replays with every proved root cut admitted

All 31 cuts recheck at load and all 31 transport successfully at entry. Learned-cut counts below **exclude** the 31 imported facts. Terminal leaf visits include unfinished leaves, not just proved leaves.

| op | Variant | Checked closed? | Counted units | Replay interval s | Terminal leaf visits | Learned cuts | Source SAT / checked refuted |
|---|---|---|---:|---:|---:|---:|---:|
| 4 | no seeds | no | 16,672.478177 | 29.019 | 1 | 36 | 21 / 35 |
| 4 | 31 checked seeds | no | 16,668.652598 | 60.980 | 2 | 17 | 32 / 16 |
| 0 | no seeds | no | 7,150.415742 | 20.112 | 1 | 13 | 11 / 12 |
| 0 | 31 checked seeds | no | 7,144.273260 | 56.513 | 3 | 6 | 22 / 5 |

The timed replay interval includes entry transport, proof search and final checking, but excludes input loading and the initial independent seed recheck. The scheduler's full job times for the two seeded runs are **64.07 / 59.66 s**, including those excluded costs and archival work. The op-4 control's preparation job also compiled the reusable runtime; its job time is therefore not an independent process-wall control.

First unfinished seeded leaves:

- **op 4:** `started=1, a$#=i, b$<i`, local `time` stop; recorded numeric model, **121** violated instances.
- **op 0:** `started=0, a$#=0, b$>0`, local `time` stop; recorded numeric model, **114** violated instances.

[summary.json](summary.json) carries the exact paths, complete points, violated-index sets, root-index classification and per-op ledgers. The original packets, proof trees, declarations, attempts and traces are in the compressed archives below.

**Interpretation:** op 4's 17 new cuts meet the cut-count prediction, but its >10,000 units and non-closure do not meet the work/closure prediction; op 0 does not close. Only 31 proved facts were available, not the proposed 51. This is a negative result for the implemented root lift, **not** a clean falsification of a correctly specified 51-template, three-tier design. The next design input needed is the exact identity/template list and its admissible root premises, separating leaf-guarded inclusions/self-zeros from unconditional partitions and map-frame lemmas. Do not raise production budgets on this evidence.

## Evidence, validation and reproduction

All reported runs used an exclusive **large** VM, **`bx_25xas5gt`**, eight pinned vCPUs, no co-tenants. The seeded batch requested two VMs; the scheduler actually reused one sequentially. No parallel-wall or repeated-gate claim is made. Prepared `replay.js`/`roots.js` bundles were reused for root and op jobs, rather than reinstalling for each replay.

- Census: `../section14-census-v2/` (`receipts.br`, manifest, log, placement).
- Frozen build, no-dump op-4 control and runtime: `../section14-prepare-v1/`.
- Independent root identities: `../section14-roots-v1/`.
- Full-context root follow-up: `../section14-law-root-v1/`.
- Plain op 0: `../section14-op0-control-v1/`.
- Seeded op 4 / op 0: `../section14-seeded-v1/op4/` and `op0/`, plus batch logs/placement.
- Final independent kernel/model/accounting audit and type/lint/regression receipts: `../section14-audit-v5/`.

Every compressed receipt has a SHA-256 manifest. Reconstruct runtime/input files from the archived preparation and frozen `../section13-runtime-v1/ready` packets. The job specifications are `research/track-m/jobs-section14-*.json`; `run-section14-op.sh <op> 50000 plain|seeded` uses prepared data at `ready/`, `runtime/` and, for seeded runs, `seeds/root-seeds.json`. `prepare-section14.sh` rebuilds from `source-input/source.tar.gz` (the pinned Section 12 input). Source integrity and the full kernel hash census are archived.

**Final audit passes:** all 31 root proofs rebase to standalone `checkCounted` certificates; all 31 empty-proof mutants are rejected; all 48 standalone source SAT points validate; and all four recorded numeric paths and complete violated sets pass exact integer recomputation. The production code already validated each numeric point before recording it. Static typecheck/lint pass on boat; the root-admission regression passes (1 test, 7 assertions). All seven temporary remote chunk-archive directories were removed only after their local SHA-256 digests were reverified. Prepared runtimes and the shared VM are retained. The first check attempt failed only on two unused research imports. The first two combined-audit attempts put generated runtime data at repository root, where lint scanned the bundle; the final job places it under ignored `runs/` instead. The next audit also incorrectly applied bare-count freshness to the entire MC root, whose quantified flags legitimately mention witnesses. The final audit instead rebases each saved proof onto its single count axiom and verifies a standalone `checkCounted` certificate. A subsequent typecheck caught a row-builder import from the wrong module; it was moved to its public export in `kernel/prove.ts`. All failed-attempt receipts are retained.
