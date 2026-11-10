# T16 tiny finite proposals — bounded pilot handoff

Production remains **disabled**. No existing file was edited by this worker; no commit was made. The proposer is untrusted. Every reported drop below was independently certified by Main's optional `finiteTinyHoudini` wrapper: `m.pre`, ALL `m.facts`, the complete frozen current family, the actual source interpreter's enabled step, and the actual target post-law. Caller laws were protected. Neither a finite screen nor its exhaustion is a proof.

## Results: do not substitute the two input families

Final batch: `20261109-144230-03co60`; measured tree `f1a9b896a1a8`; logs and exclusive placement receipts: `runs/t16-tiny-worker-wrapper-v7/`.

| Input | run | certified drops | remaining family | wrapper ms | supported fixed point? |
|---|---:|---:|---:|---:|---|
| ORIGINAL 40, no historical drops applied | 1 | 5 | 35 | 1713.341 | yes |
| ORIGINAL 40 | 2 | 5 | 35 | 1355.644 | yes |
| ORIGINAL 40 | 3 | 5 | 35 | 1801.432 | yes |
| POST-BOUNDARY 34 | 1 | 3 | 31 | 1355.724 | yes |
| POST-BOUNDARY 34 | 2 | 3 | 31 | 1949.879 | no: wall |
| POST-BOUNDARY 34 | 3 | 2 | 32 | 2000.066 | no: wall |

All original-40 runs used exclusive `large` AMD EPYC 4585PX VMs, 2 of 8 vCPUs pinned, zero co-tenants. Survivor-34 runs 1/2 used exclusive `large` Ryzen 9 9950X; run 3 used exclusive `large` EPYC 4585PX; all 2/8 pinned, zero co-tenants. Commands used `--timing`, class `submission`, no forced VM count. `wallMs: 2000` was unchanged; Main's wrapper reserves its normal search-wall headroom. No deadline extension was introduced.

### ORIGINAL 40: same five certified names in all three runs

1. `fields: CT[a]=CT[b] and CV[a]=CV[b] -> Config rows agree`
2. `inX: stored guard reconfigs/inS`
3. `inX: stored guard reconfigs/inS or disabled/1`
4. `every x with x < size: never Config[x] is 0 and 1 <= St[x]`
5. `inX: no quorum canVote/1`

All five were found by 508.554 / 511.828 / 607.760 ms respectively; traversal then completed. These are **five total**, NOT five of the seven costly false survivors: two were already ordinary-boundary drops.

### POST-BOUNDARY 34: completed below five

The completed run certified only:

- `inX: stored guard reconfigs/inS`
- `inX: stored guard reconfigs/inS or disabled/1`
- `inX: no quorum canVote/1`

Run 2 certified the same three but timed out during the final no-new-drop round. Run 3 certified only the first two before its wall. All three survivor jobs intentionally exit 1 because their explicit five-drop goal assertion failed; this is not masked by the outer supercomputer client's exit 0.

The 34 family is reconstructed only after independently replaying the six captured boundary drops against their entire round family, pre/facts and actual source step/post-law. Historical names alone never authorize removal. Those six are CT<=44, CfgT<=44, Config[x]/St[x], CT/CV row agreement, the primary CV ordering field, and CV<=2.

### Exact remaining candidate names

`research/track-gen/t16-tiny-results.json` records **every exact remaining candidate name for each of the six runs**, not just counts. It also records input SHA-256, raw caller/candidate roster, per-job exit codes, scope and round statistics, hardware placement, certified names, and owned-source hashes. `t16-tiny-receipts.ts` validates the six-row unique measured roster, mode/initial-family binding, drop totals, side exits, and exclusive placement before formatting that JSON.

At the completed 34->31 fixed point, the three still-missed costly weakenings are:

- `inX: stored guard reconfigs/inS or disabled/0`
- `inX: stored guard reconfigs/inS or disabled/2`
- `inX: stored guard reconfigs/inS or disabled/3`

`inX: no quorum canVote/3` and `fields: CV[a]=CV[b] and CfgT[a]=CfgT[b] -> Config rows agree` also remain (not asserted false). The original 40->35 fixed point additionally retains the four names removed by the ordinary boundary but not tiny: `CT at most 44`, `CfgT at most 44`, `CV at most 2`, and `fields: St[a]=1 -> CT[a]=CT[b] -> CV[b]<=CV[a]`.

Both completed fixed points have `unsupported: []`; neither was prevented by time. The two incomplete survivor runs were prevented by wall, not unsupported syntax. A completed **compiled 0/1-screen** fixed point below five costly drops is the useful falsifier: no unbounded validity or complete semantic-cover claim follows. No richer domain was substituted.

## Exact measured finite scope

- Params: `{size: 3}`.
- Source scalar `started`: 0/1.
- Source `Config` cells: keys `[0,1,2,64,65,66,128,129,130]`, each 0/1. Stride 64 is inferred from count bodies, never a production identifier/name special case.
- Source `CT`, `St`, `CV`, `CfgT`: keys `[0,1,2]`, each 0/1.
- Source map defaults remain their source-model defaults (all zero here).
- Thus 22 base state bits, approximately 2^22 naive assignments; pre-family dependency pruning admits far fewer screen states.
- Numerical request domains: `op=0..6`, `i,j=0..2`, `hx,hy=0..3`.
- Carried `S`, `Q2`: 0/1 at keys `[0,1,2]`, zero elsewhere.
- Binder screen values: `[0,1,2]` only; this is **not** a certified universal cover.
- Inactive operation slicing and irrelevant-request-coordinate quotienting avoid request Cartesian products.

The final completed no-new-drop round in both modes screened 2,522 pre-admitted states, 12,923 changed enabled transition screens, 172,526 DFS events, seven operation slices, and no proposals. These are untrusted screen statistics, not independently certified counts of semantic states/transitions. Real Map/interpreter/full-family checking occurs at proposal callbacks only.

## API and trust boundary

`tinyFiniteCandidates(source, m, family, params, onCandidate): TinyFiniteStatistics`

- `family` is the WHOLE current caller/helper family.
- Callback receives fresh source `State`, source `Request`, and proposed violated `Law[]`; a transition can propose multiple targets.
- Callback false rejects and resumes. Void/true stops further proposals for reported targets, not state traversal. Neither is a drop decision or proof.
- `completed` means a supported finite-screen traversal finished. `exhausted` additionally means no proposals were emitted. Both are false on unsupported cases/timeouts. No semantic completeness claim is made.
- The module sets no deadline and calls no solver. It uses existing `checkWall` throughout compilation/enumeration. On wall expiration it returns partial statistics with `timedOut`; a caller must immediately `checkWall` again to preserve enclosing cancellation. Main's wrapper does so.
- Main owns the optional wrapper and all integration. It is not production-enabled by this worker.

Generic implementation: structurally inferred unary/row/tuple cells; expanded source count bodies, never solver-supplied count cells; compiled dense closed-AST arithmetic and predicates; sparse address sets; source dispatch specialization; conservative inactive-write identity screen; dependency-ranked pre-state/request pruning; shared operation transitions and widened post-family screens. No protocol/law-name cases, hand laws, larger proof fuel, kernel/solver changes, or external function JS execution.

Unsupported features include history/least/sums, external function reads, existential/shadowing laws, nonconstant/large count bounds, wide dynamic addresses, >64 coordinates and >1 MB generated screens. Unknown never authorizes a drop.

## Validation and previous experiments

`runs/t16-tiny-worker-check-v6/tiny-unit-and-check.log`, batch `20261109-143136-89qm9d`: **12 tests / 40 assertions pass**, full `bun run check` type/lint pass, zero warnings/errors. Coverage includes full-family preconditions, stride/native tuple inference, independent replay, rejection/resumption, wall propagation contract, syntax-only dispatch/quotienting, caller-side facts/pre rejection, multi-target proposals, unconditional writes despite inactive flags, and no-ops.

Earlier green checks: `20261109-141234-vxc85l` (10/31), `20261109-142322-zas88u` (11/35). Final complete-tree validation including the new receipt formatter and wrapper benchmark: `20261109-145638-3wrrd7`, tree `e6255a53d9c4`, `runs/t16-tiny-worker-final-check/tiny-unit-and-check.log`: **12 tests / 40 assertions pass**, full type/lint pass, zero warnings/errors; job 39.25s. All worker-launched tasks are terminal and all remote jobs have been collected.

All experiments/validations started by this worker are collected before handoff. Historical pilot batches:

- `20261109-132745-or0ja1`: AST inspection, complete.
- `20261109-133434-ey9tij`: old per-target pilot; zero proposals/2s, 6/7 tests; unguarded count-forall fixture returned unknown correctly. Exploratory 20s job externally timed out at 10s; no 20s result claimed.
- `20261109-133945-qu9cez`: cached per-target pilot, same fixture failure, 8,641 DFS events/2s, zero proposals; exploratory job externally timed out at 10s.
- `20261109-134748-4lq9wq`: per-target compilation hit 2s; tests encountered the coordinator's since-fixed import cycle.
- `20261109-140208-30j8z2`: corrected 34 family but per-target expansion still hit wall/large-screen cap; zero proposals.
- `20261109-142319-a9ffcn`: shared-transition fixed-family pilot certified two helpers in 397ms, no unsupported cases.
- `20261109-143132-s52lq2`: direct successive-round 34-family control found the same three helpers; two supported fixed points at 1619/1677ms and one wall-limited run. All three explicit five-drop assertions failed.
- `20261109-144230-03co60`: final Main-wrapper paired family controls above, all six receipts collected.

No running jobs remain after final check collection; no remote GitHub writes, rebase/reset/clean, shared scheduler/VM restart, or process kills were used.

## Exact worker-owned new files

- `core/finite-tiny.ts`
- `core/finite-tiny.test.ts`
- `research/track-gen/t16-tiny-bench.ts`
- `research/track-gen/t16-tiny-inspect.ts`
- `research/track-gen/t16-tiny-notes.md`
- `research/track-gen/t16-tiny-receipts.ts`
- `research/track-gen/t16-tiny-results.json`
- `research/track-gen/t16-tiny-worker-check-jobs.json`
- `research/track-gen/t16-tiny-worker-check-v5-jobs.json`
- `research/track-gen/t16-tiny-worker-check-v6-jobs.json`
- `research/track-gen/t16-tiny-worker-inspect-jobs.json`
- `research/track-gen/t16-tiny-worker-pilot-jobs.json`
- `research/track-gen/t16-tiny-worker-v2-jobs.json`
- `research/track-gen/t16-tiny-worker-v3-jobs.json`
- `research/track-gen/t16-tiny-worker-v4-jobs.json`
- `research/track-gen/t16-tiny-worker-v5-jobs.json`
- `research/track-gen/t16-tiny-worker-v6-jobs.json`
- `research/track-gen/t16-tiny-worker-wrapper-v7-jobs.json`
- `research/track-gen/t16-tiny-wrapper-bench.ts`

Only new files above are mine. `research/track-gen/t16-tiny-houdini-check-jobs.json` is Main's file and was not touched. `runs/t16-tiny-worker-*` contains worker-owned generated receipts. Existing `finite-houdini.ts`, `finite-frontiers.ts`, `counts.ts`, `machine.ts`, REPORT and audit evidence were not edited by this worker.
