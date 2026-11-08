# Section 11 — first unfinished leaves after the two fixes

Production revision 5974b9165d6860f1157f3bed3cd66a7e1514e904. Canonical input;
same bx_25xas5gt, exclusive eight pinned vCPUs. This is a separate instrumented
full-family replay, not one of the timed A/B repeats. Kernel and law harness
remain unchanged. Source probes use separate diagnostic allowances; their work
is never charged to, or presented as having fit inside, the production draw.

## Inv*: first unfinished branch has advanced

Final unresolved actions are **3,4,5,6**, versus 0,1,3,4,5,6 before the fix.
Initialization and op1 now close in this replay. The first unfinished leaf is:

    op = 3, started = 1
    CT[j] < CT[i]
    a$# = j, j$ = j
    i < size, j$ < size
    ?canVote <= 1, ?committedQuorum <= 1

These are inequalities on flags, not assertions that either flag is true.
star-full-point.json retains every exact atom. The numeric model is valid:
size=2, i=1, j=j$=a$#=0, CT[i]=1, CT[j]=0, r$0=r$1=1, ?all$1=1;
remaining entries and the read mapping are retained alongside it.

The terminal model reproduces in **3.042176 units**. Its 31 violated indices:

    45,47,54,49,2,3,4,5,27,29,32,34,36,38,40,42,82,83,86,87,
    1,6,7,8,51,71,74,81,84,85,88

Fresh source results: **4 kernel-checked refutations / 27 validated SAT / 0
unknown**. Every instance, expression, core and units is in star-full-sources.md.
The checked source results are:

| Index | Instance | Units |
|---:|---|---:|
| 3 | r$0 <= r$17 | 25.020353 |
| 5 | r$1 <= r$8 | 13.416827 |
| 32 | r$1 <= r$9 | 20.439056 |
| 1 | r$0 <= r$8 | 17.150839 |

The production draw is **31.837620**, measured spend **31.863512**:
3.042176 numeric + 7.881124 batch-selection + 20.940212 source work.
Only instance **54** is attempted; it stops unknown/time. The separate source
probe establishes SAT in 24.967622 units, not a new cut. No scalar child is
reached. The atomic overrun is 0.025892, not an extra allowance.

## Inv2973: initialization remains first unfinished

    op = 0, started = 0, ?noneCopied = 1
    a$# = 0, b$ = 0
    i < size, ?canVote <= 1, ?committedQuorum <= 1

The exact path is in overlap-full-point.json. Production's terminal query is
unknown/time, not a model. A separate numeric replay finds and validates the
model in **6.874298 units**: size=1, i=a$#=b$=j=0, r$0=r$1=r$2=r$3=1,
r$4=2, ?all$1=1, ?noneCopied=1; the full point is retained.

It violates **101 instances** (complete list in the point file). All source
results and units are in overlap-full-sources.md: **8 checked refutations /
93 validated SAT / 0 unknown**. Checked results:

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

Production draw **23.787585**, measured spend **25.269563**:
24.498107 natural-case work + 0.771456 timed-out numeric query. There are no
batch-selection or source attempts. The atomic overrun is 1.481978.

## Scope of the evidence

The full-family profile has the same five verdicts as every A/B repeat. Its
Inv2973 counted total matches every B repeat exactly (5108.274084). Inv* is
5160.143045 here, versus 5162.032223 / 5160.085453 / 5160.085453 in the timed
runs. This small variability is not hidden: the diagnostic is its own actual
trace, not asserted to be a byte-for-byte replay of a particular timed run.

The row ledger has no double counting; the summarizer checks nested exclusive
work against each parent's total. Numeric models and source SAT models are
independently revalidated in fresh processes. Source refutations were checked
under the unchanged kernel during the source probes; the model validator does
not claim to re-prove their omitted trees.

The complete trace is retained in receipts.br, **419,097 bytes**, SHA256
839d17c2dc1789dfaf25bba4d4039787c94367071b12ae9a1cf96cac4af6f3f8.
Recover it on boat with:

    bun research/track-m/extract-section10-archive.ts runs/track-m/section11-diagnostic-v2

This produces star-full.json and overlap-full.json with the exact numeric
goals, structural-column definitions, models, source hypotheses and ledger.
One preceding diagnostic attempt stopped at a new auditor's sort-comparator
lint error before profiling; its failure is retained separately. The six timed
runs were not repeated. No later gate was run.

Final validation in ../section11-validation-v2/ passes type/lint and 258 tests /
1,313 assertions. Fresh processes validate all 120 source SAT models, both
numeric models, their paths and all 132 violated-source selections. The 12
refuted source receipts were kernel-checked during probing. All three owned
temporary VM archives were removed after verification.
