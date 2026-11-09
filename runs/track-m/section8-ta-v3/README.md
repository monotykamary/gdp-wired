# Section 8 — T-A

Measurement-only; production sources, budgets, caps, and the kernel are unchanged.
All successful receipts and setup failures used bx_3kjzmmhv, exclusive with eight pinned vCPUs.

## Inv*: second arithmetic leaf of the hygienic active traversal

Scope: op=5, started=1, St[i]=1, CfgT[i]=CT[i], committedQuorum=1,
S[i]=1, canVote=0, a$#=i, j$<i; the complete ordered path and model are in
`Invstar-leaf.json`. It has 53 numeric hypotheses and 24 active cuts.

The 32-element restricted pool has V={27,32,77,84}. The 91-element full pool
has 44 violated goods. Every live variable of these goods is explicitly bound.
V is not empty. Fresh source queries for the two requested facts do not prove:

| Original index | Kind | Result | Counted units | Fresh-query wall |
|---|---|---|---:|---:|
| 84 | R2 / count-bound | projected SAT | 36.647560 | 70.484 ms |
| 77 | frame | projected SAT | 16.470482 | 35.682 ms |

Both models satisfy their source AST and ordered path under the evaluator's
zero completion. Both omit `w?all$1` and `w?all$3`, so neither meets the explicit
binding condition for model reuse. No model was reused. These are not protocol
counterexamples. Source goals, models, and missing-binding lists are retained
in `results.json`. The other two violated facts were not attempted in T-A.
The design's predicted proof of 84 did not materialize.

## Inv2973: fourteenth arithmetic leaf

The exact leaf was retried with the same 53 active cuts, without admitting any
new fact. It checks in 26.770835 counted units / 678.389 ms wall, both as a
numeric tree and as a conditional proof of the original goal. The old traversal
had only 13.104 counted units left. There is therefore no SAT model/V for this
leaf: it is already proved, not an empty-V generator gap. This does not prove
the complete source. Its original T-A receipt and full leaf are in
`../section8-ta-v2/`.

## Decision and validation

T-A's nonempty condition holds where there is a model, but the requested
Invstar proving prediction fails. The explicit empty-V stop was not triggered.
Continue the requested ordered measurements only; the implementation pass line
has not been met. No T-F1 or later measurement was part of this commit.

`static-check.log`: TypeScript and type-aware lint pass; five census tests /
15 assertions pass. Two earlier attempts were setup/static-check timeouts,
not scientific T-A outcomes (`../section8-ta-data-v1/ta-data.log` and
`../section8-ta-v1/ta-leaves.log`). The successful run separates these phases.
