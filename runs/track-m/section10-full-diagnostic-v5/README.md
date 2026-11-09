# Section 10 diagnosis — actual full-family allocation, 192ebbe2

Diagnostic only. Same canonical input and bx_25xas5gt, exclusive eight pinned
vCPUs. Core, kernel, original family harness and all budgets remain unchanged.
The installer instruments only disposable copies. No later gate was run.

## Important corrections

The 1,500 number is a per-row **ceiling**, not a guaranteed draw. The isolated
op-5 probes in ../section10-diagnostic-v2/ start with 5,000 units and hit that
ceiling. The ordinary family has already spent most of its allowance before
these leaves. No observed full-family row receives 1,500 units.

There is also an implementation/specification mismatch: leafAllowance calls
supportBudget(R, R/max(1,L), true), which computes

    max(0, min(R, max(R/max(1,L), R/3)))

R/3 is a FLOOR in this expression, not the requested ceiling. The existing test
explicitly expects leafAllowance(900,9) == 300, not 100. The total is conserved,
but the requested even-share/remaining-third-ceiling rule was not implemented.
No change to that strategy is included in this diagnostic commit.

## A. First leaves still unresolved at the end of the family

The selector is the first action still unresolved after fallback, then its
first unsuccessful row. This avoids mislabeling a transient failure that the
family subsequently repaired. Inv* unresolved actions: 0,1,3,4,5,6. Inv2973:
0,1,2,3,4,5,6. Exact scopes and values: *-full-point.json.

### Inv*

First leaf: initialization (op=0), a$#=0, j$<0. Inherited guards include
started=0, ?noneCopied=1, ?canVote<=1, ?committedQuorum<=1, i<size and j$<size.
The terminal numeric query returns `refuted, not unfolded`, core [], in
2.731550 units. No numeric model or violated-instance set exists for that
terminal query. This leaf has 191.008012 units available and stops long before
exhaustion. It is not a generator-gap model.

The exact consumer in core/count-recovery/derivability-closure.ts:239 requires
`q.core?.length`; an empty core bypasses proof construction, then the code
returns no numeric model. A separate fresh-process probe builds a proof from
ZERO goal hypotheses using refuteFast. The unchanged kernel checks both that
empty-hypothesis proof and its transport to the complete numeric goal:
**0.0098612 units**, both checks true. This diagnoses the dropped empty-core
result; the production fix is deliberately NOT included.

For completeness, star-full-sources.md contains all 31 violated instances of
the preceding, successfully closed row (a$#=0,j$=0), NOT the terminal j$<0 row:
14 checked source refutations and 17 validated SAT results. Its source model
and exact path are explicitly labeled `last-observed-model` in the point file.

### Inv2973

First leaf: initialization (op=0), a$#=0, b$=0; inherited initialization guards
as above, without j$. A fresh query reproduces the actual numeric model in
6.874298 units. Nonzero values: ?noneCopied=?all$1=1, size=1,
r$0=r$1=r$2=r$3=1, r$4=2; all remaining values are in overlap-full-point.json.

There are **101 violated instances**. Every source expression, result and
units is in overlap-full-sources.md: **8 checked refutations, 93 validated SAT,
0 unknown**. Checked source indices / units:

| Index | Units |
|---:|---:|
| 193 | 8.698566 |
| 50 | 13.141840 |
| 51 | 16.776168 |
| 2 | 13.403808 |
| 167 | 11.572981 |
| 173 | 11.572981 |
| 204 | 19.904985 |
| 206 | 19.906953 |

These are independent diagnostics, not production cuts or debits to the
original row. The actual row stops before ANY source attempt.

## B. Counted-work ledger

All rows, paths, draws, nested spans, outcomes and exclusive categories are in
*-full-ledger.json and ledger-summary.json. Parent and child spans are NOT
summed together. The summarizer checks exact conservation (1e-7 tolerance).

| Actual family row | Draw | Spent | SAT / checked / reused / unknown source attempts |
|---|---:|---:|---|
| Inv* op0, a$#=0,j$=0 (closed) | 200.939582 | 29.794711 | 0 / 1 / 0 / 0 |
| Inv* op0, a$#=0,j$<0 (first open) | 191.008012 | 2.731550 | 0 / 0 / 0 / 0 |
| Inv* op5, a$#=i,j$=i | 124.647629 | 126.094380 | 2 / 0 / 1 / 1 |
| Inv2973 op0, a$#=0,b$=0 (first open) | 71.362754 | 75.807314 | 0 / 0 / 0 / 0 |

The first open Inv2973 row spends 49.854090 on natural-case arithmetic,
6.874298 on the numeric query, and 19.078926 on batch selection. The last
atomic batch overruns its draw by 4.444559 units; no extra draw is granted.
Inv* op5 similarly overruns by 1.446752 units. No scalar split is reached there.

The isolated 1,500-unit active-op5 ledger is retained separately. Inv*: parent
645.159893, scalar yes 17.071888, scalar no 837.799287 (total 1500.031068).
Source attempt outcomes: 16 SAT / 15 accepted / 39 reused / 20 unknown; raw
arithmetic refutations 35, not 35 accepted cuts. Inv2973: 1503.793922, with
14 SAT / 25 accepted / 55 reused / 32 unknown; raw refutations 56. Those rows
are not the ordinary family's allocation or its first unresolved leaves.

## C. Where 1,500 comes from

core/count-recovery/row-cases.ts:103 contains the literal
`prove(path, Math.min(until, clock()+1500))`. It came in with 616b0c9c
(`feat(counts): port guarded witness derivations to production`). There is no
adjacent derivation/comment explaining why the numeric value is 1,500. It is
not derived from total allowance. The additional leaf draw is applied at
core/count-recovery/derivability-closure.ts:303-307 using leaf-allowance.ts:4
and support-budget.ts:3. Scalar children share one absolute deadline.

## D. Why the three proved-law costs increased

See ../section10-deep-diagnostic-v1/cost-attribution.json and README.md. The
new generator retains one existing full-pool inclusion, adding four downstream
hypotheses. Generation itself charges zero units (not a zero-wall claim).
One primary: four heavier SAT model queries +20.693282, grow +0.216480, total
+20.909762; no extra queries. Inv3915 and Inv1758: extra grow goal-node visits
only, +1.781040 and +2.137248. No pruning/change is included here.

## Validation and evidence recovery

../section10-diagnostic-validation-v1/validate.log: type/lint pass; 255 tests,
1,215 assertions pass. Fresh processes validate 268 source SAT models and 3
terminal numeric models, plus all source selection models and scope atoms.
56 checked source-refutation receipts are retained; they were kernel-checked
during the probes, not independently re-proved by the model validator. The
empty-core proof IS checked independently in that validation.

The full trace is 178 MB decoded but only 426,662 bytes compressed. receipts.br
is complete; archive-manifest.json binds SHA256
00e47a15aba09d07f176be25058c47226d47055391d1f96e7a8ae3eafa3974db.
No truncated earlier collection is used as final evidence. Recover the full
star-full.json / overlap-full.json using, on boat:

    bun research/track-m/extract-section10-archive.ts runs/track-m/section10-full-diagnostic-v5

The archive and summary checks are repeated in diagnostic-postprocess-v1.
The temporary archive in the VM home was removed after verified retrieval.
All submitted diagnostic/validation processes completed.
