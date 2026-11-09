# T-8.1 — bounded model-driven loop

Research only, bx_3kjzmmhv, exclusive with eight pinned vCPUs. The full original
pools are used here: 91 Inv* instances / 490 hypotheses, and 289 Inv2973
instances / 1341 hypotheses. No pool cap, source-query allowance, total law
allowance or 350-unit arithmetic-leaf share is increased.

The loop queries only the numeric goal and proved cuts, computes all violated
pool goods, attempts them only at that scope, and re-queries immediately after
a proved fact kills the current model. Per-scope tried/excluded sets are
monotone and no instance is attempted twice at a scope. All source-model reuse
requires explicit binding of every live variable in the renamed source slice.

Some pool read variables are absent from the numeric query. For the fresh
numeric valuation only, the diagnostic explicitly completes those entries to
zero, then checks the complete valuation against the numeric AST and scope.
It does not add assumed pool facts or apply this completion to source reuse.
Without that step the earlier diagnostic stopped on missing pool bindings;
that was not an empty violated set.

| Full-pool active diagnostic | Cuts | Total counted units | Loop/source wall | Result |
|---|---:|---:|---:|---|
| Inv* | 5 | 440.058722 | 0.781 s | First arithmetic leaf times out |
| Inv2973 | 2 | 352.459662 | 1.329 s | First arithmetic leaf times out |

The first leaf uses 354.431277 / 352.109316 units respectively, at the unchanged
350-unit deadline (the final atomic operation may overrun slightly). Inv* makes
seven source attempts and records four model rounds before the next query times
out; Inv2973 makes two source attempts and two model rounds. No duplicate
(instance, scope) source attempts were observed. Both source-entry checks remain
false. The loop has **not** completed Inv*, nor returned a named empty-V gap for
Inv2973, so T-8.1 fails its prediction.

Both stopped scopes are the equal/equal row: `a$#=i, j$=i` for Inv*, and
`a$#=i, b$=i` for Inv2973, under the existing op=5 active guard. They are **not**
the later `j$<i` Inv* leaf from T-A or Inv2973's old fourteenth leaf. Exact paths,
V sets, excluded sets, source indices, and costs are retained in `results.json`.
These timeouts are not generator-gap proofs and are not protocol counterexamples.

This measurement returns at loop failure rather than running the unrelated
legacy fallback. Earlier restricted/hygienic runs, setup failures, and the
initial missing-binding run are retained in sibling `section8-loop-*` directories.
The full-pool control independently reproduces the same counted totals in
`../section8-loop-full-v1/`. TypeScript and type-aware lint pass.
No production implementation or Gate 1 run follows.
