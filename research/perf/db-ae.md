# Native co-write provenance closes db_ae

Base `beb36ebc30de`; tested code snapshot `beb36ebc30de+a1caf227`.
No trusted rule, certificate language, or budget changed.

## Missing induction support

A database request can exist in an induction pre-state with no owner row.
Attaching a new row for another request preserves the familiar plain supports
but breaks their join. The interpreter and Q3's concrete model completion
confirm this obstruction (`runs/dbae/baseline/counterexample.log`); it is not a
reachable protocol bug.

The search now derives converse co-write provenance: the input forgotten by a
row's key witnesses both the corresponding owner row and original request.
Generated key bounds, row guards, functional dependencies and joins close the
supporting set. They remain obligations, never admitted assumptions. Native
tuples avoid the earlier packed-key alias; existing ghost admission suffices.

Dependency-local proofs precede full-set checking. Actual fallback proof trees
are retained in the existing native-tuple memo and checked again in the final
set. Packed-key scheduling is unchanged. Duplicate empty-parameter samples are
explored once; distinct parameter valuations remain intact. `kernel/prove.ts`
is untrusted search (see `docs/ARCHITECTURE.md`), not the trusted checker.

## Accepted measurements

All computation ran on boat; only orchestration, edits/git and receipt handling
ran locally. Each protocol pair used one isolated large VM, the same four pinned
CPUs, alternating side order, and an external strict 60-second child limit.
Placement records include both Ryzen9700X and9950X: fixed class, not one CPU model.

| Measure, repeats 1/2/3 | Main | Candidate |
| --- | --- | --- |
| IC3Syn proved | 25 / 25 / 25 | 26 / 26 / 26 |
| db_ae seconds | timeout / timeout / timeout | 17.018 / 40.787 / 14.930 |
| DuoAI proved | 10 / 10 / 10 | 10 / 10 / 10 |

`runs/dbae/gate3-paired/` and `gate3-summary.json`: 117 pairs, 234 receipts,
no per-case loss, zero wrong. Proven requires both proven and checked; no
supporting law was supplied. Common-case median geomean ratio: 0.9613.
`gate3-other/`: seven shards and static checks pass; 24,014 native/packed
transition comparisons agree. Broken variants: 11 refuted,14 unknown,4 external
timeouts, none proven. Timeouts are not called refutations.

Exactly two quick-bar attempts were used. `runs/bar/runs/dbae-1/` covers all
benchmark views: wrong0, solid losses0, Lean6/6. It also exposed missing g332
data in the scratch snapshot and one five-second test cutoff. `dbae-2/` reruns
only g332 and onecpu on identical code/budgets, with the baseline's existing
corpus linked read-only: g332332/332 each side, identical search on all goals,
median ratio0.967; all six one-CPU jobs each side pass. Its retained launcher
warning is an initial goal-pack upload race; the automatic retry exits are all0.
All owned Modal fallback apps (used only after three boat failures) were stopped.

Timing is noisy: second-bar one-CPU per-test median geomean1.231, data suite
ratio1.370, infer0.642, overlapping suite bands. Same-VM follow-up on five
adversarial tests (`runs/dbae/speed-pairs-exact/`) has all candidate tests passing,
no separated three-run slowdown, and one baseline five-second cutoff. Speed is
level by the noise rule, not uniformly faster. The preliminary `speed-pairs/`
probe accidentally matched archived tests too and is excluded from conclusions.

Earlier rejected gates and repairs remain in `runs/REPORT.md`. An alpha-renamed
target regression passes; a broader phase-free variant remains unresolved.
No exhaustive TLC comparison or new trusted mutation/Lean campaign is claimed.
Q3 (sol) supplied the concrete diagnostic; COUNTS (astra) was read and merged
through the base, but no counting identity is needed for this obstruction.
