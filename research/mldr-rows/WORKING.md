# Inv1758 — lane E takeover, 2026-11-10

Coordinator reassigned Inv1758 to E. B retains Inv* and p1; F retains
Inv2973-half. Safety's source 9124348d and its fresh-family receipts remain
unchanged. No other lane worktree is edited.

## Current result and active next falsifier

Guard v3 is complete: all three source checks pass 89 tests / 305 assertions.
All 12 proof arms are unproved. Plain guard repair exactly matches the
control at 2700.233514 units / nine rounds; early completion exactly matches
its prior 2700.272896 / five rounds. Row-first stops at the wall. This is a
tested correctness repair, not a measured search improvement. Preserve the
negative result and test the proof-producing guarded closure next.
Committed source/evidence: `9528c134`.

Active five-job experiment: `491a39f8-e02a-4680-9b9b-288b1c5b3808`, output
`runs/mldr-rows-focus-guard-v1/`. Paired old/new guards use the existing
focused-only and one-third-share entry modes at 2700 units, plus downstream
closure/field/guard/focused regression tests. This isolates the new guard
from Lane B's historical failed early-focus scheduling experiment.

### Active field-only demand discriminator

Focused guard comparison also failed all eight arms; 25 downstream tests /
76 assertions passed. A unit-limited third-share pair was exactly unchanged
at 2700.696015 units. The retained per-operation trace has no checked full
proof; op4 reaches a scalar SAT hint followed by a 192-hypothesis unknown.

Static call-chain evidence: `deriveCountClosure` immediately returns unless
the claim itself identifies at least two count reads. Inv1758 has a primitive
field claim. The new **disposable-only** prototype finds pre-counts whose
declarations read an exact claimed primitive cell, and their already
proposed coupled reads (cap 12). No fact, law, or count instance is added.

Task `981ca35b-2773-4d0d-b1f7-bf306f456c61` compares that bridge in both
orders at 2700 units and adds scalar-field positive/negative kernel replay.
Production `derivability-closure.ts` is unchanged. The four measured arms
returned unproved. Source check failed because mounted `.ts` payload files
were also typechecked at the wrong data-root relative path; tests did not
run. Packaging-only v2 uses `.txt` payloads and identical copied source.
Validation-only batch `20261110-032233-wyx97d` passes source check and
31 tests / 90 assertions, including positive and negative scalar-field
closure fixtures. No proof run was repeated. The recovered candidate trace
has ten field-demand events and eight internal cut events, but all four
full arms remain unproved. Production closure is still unchanged.

### Earlier hypothesis and submission history

Both initial schedules are rejected: all 16 arms remained unchecked. The two
source checks passed 14 tests / 63 assertions each. Proposal-only inspection
on the retained archives shows that the control never finds an actor-row
inclusion, while early/row-first supplies 16 proposals and admits 10.
The remaining scalar guard was too strong at the leader boundary: a strict
member upper bound only requires an inclusive comparison with the target.
The new typed patch retains source strictness and is being tested at the
unchanged 2700-unit share (plain, early and row-first; paired orders), with
source checks and kernel-positive/negative controls. Task:
`8769a096-6698-465c-b9ba-0e8edbd6be25` (batch `20261110-024949-vm5h1o`). Not yet a measured improvement.

Static review caught missing undefined checks for the newly read flag in
the test fixture under `noUncheckedIndexedAccess`. The original frozen
checks remain untouched. Test-only v2 checks add those guards; production
bytes are identical and no proof job is repeated. V2 task:
`b8fc0df3-4514-4277-9209-e4ea8e904e9a`. Commitlint passed separately.

The proposal truth table is deliberately only sufficient:

| Member premise | Target predicate | Scalar proposal |
| --- | --- | --- |
| `v < U` | `v < B` | `U <= B` |
| `v <= U` | `v < B` | `U < B` |
| `v < U` | `v <= B` | `U <= B` |
| `v <= U` | `v <= B` | `U <= B` |

No scalar proposal is asserted as a fact. Every accepted inclusion still
needs the original flag instances and a kernel-checked count certificate.

Call-chain caveat: `instantiateMemberPremises` uses only maps/keys in these
guards. The comparison operator is consumed in `deriveCountClosure`, via
deferred focused recovery. Consequently this patch alone may leave the
initial counted search unchanged. Do not call the boundary mismatch the
measured cause of nonconvergence; retain and inspect the paired result.

Both clients timed out, then passive observers recovered all 12 terminal
jobs. Every job failed setup because the submission used nonexistent
`inputs-v1`, not `input-v1`; no source check, test or solver measurement ran.
`submit-guard.sh` now validates the actual input/hash before submission, and
proof workers validate the same hash. Test-only workers do not copy it.
Replacement nine-job task: `624a22b5-2f78-426c-9b1f-42bdaada5efc`, output
`runs/mldr-rows-guard-v3/`. Proof/job budgets are unchanged; only the client
queue wait is longer. No duplicate work and no successful outcome claimed.

Coordinator census: isolated Inv1758 operations close 7/7 in pass 0 without
a share limit, 5/7 in pass 1; aim at convergence, not a larger budget.

### Previous checkpoint (superseded)

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
