# Inv1758 — lane E takeover, 2026-11-10

Coordinator reassigned Inv1758 to E. B retains Inv* and p1; F retains
Inv2973-half. Safety's source 9124348d and its fresh-family receipts remain
unchanged. No other lane worktree is edited.

## Current result and active next falsifier

Baseline: no checked proof in all four jobs. At 2700, ordinary-first returns
uncertified SAT at 2700.129 units, counted-first UNKNOWN at 2700.234. Both
6000 jobs exhaust seven-second walls, not their work allowances.

Frozen counted STEP: 68 initial hypotheses, no universal-law tuples, six
keyless count reads / ten count instances; tenth query has 244 hypotheses.
The final abstract model is become_leader, actor equal to the first target
row, with a config-term collision and differing row payload cells.

Current ten-job experiment is ce05e3b2-32d6-47f4-a62d-8d9896fada63:
`early` moves the existing bounded completion; `row-first` also moves row and
request terms before the column. Eight paired timing jobs plus two source/
test checks. No production source changes; no proof claimed until checked.

## First falsifiable measurement

Use the already verified fresh 34-law family, no supplied law. Target index
27: `fields: CV[a]=CV[b] and CfgT[a]=CfgT[b] -> Config rows agree`.
Raw family SHA256:
`96ee4bffe3c60054141501b2064f2ebbe0f61581b503859a44a8e113f1d49bcd`.
The adapter only maps caller/support names to indices and adds target metadata;
machine and law expressions are unchanged. Its SHA256 is
`f14f538ea14763ced6f8aac5227ae9bc9fbc6dd18acea4f150cbaadd3eeca639`.

Four independent large/pinned jobs measure ordinary-first and count-first
at 2700 units / 4800 ms and 6000 units / 7000 ms. These are diagnostics,
not larger production budgets. Full query/STEP snapshots and certificates,
if any, stay in the compressed boat archive. Task:
`8901c267-d68f-4835-8d67-213bee7ed517`.

## Candidate diagnosis, not yet a result

The three-key field target starts without count-law tuples. B's early
completion is deliberately restricted to count-bearing targets, so it does
not test early completion for Inv1758. Inspect the model/STEP captures first:
is a count-law instance at the actor/other-row missing while ordinary MBQI
keeps discovering unrelated scalar tuples? If so, test demand-backed early
completion in a disposable source variant. A checked complete proof and
lower counted work must support any promotion; wall truncation is not a win.

Do not repeat B's failed eager member or 64-row-scalar seeding experiments.
Do not change laws, the kernel, source-generation policy, or allowances.
Then verify the chosen change in the original harness order, with tests and
combined integration/gate evidence. Any shared `core/counts.ts` edit must be
announced in the root report, because B also owns scheduling there.
