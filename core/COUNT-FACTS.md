# Opt-in count facts (untrusted)

`core/count-facts.ts` is a source module for counted-search callers. It is **not wired into the default search** and has no new npm entry point. It imports no research code and changes no checker or certificate format.

- `countsForReads(decls, reads)` instantiates existing `CountDecl`s exactly at certificate reads, including a packed `base * hi + lo` key. Returns `undefined` when that key shape is unsupported. It is a search adapter, not a substitute for `mcGoal`/`checkMC` or their freshness/low-key guards.
- `proposeCountFacts(counts, context, options)` returns `{insts, regions, skipped}`. It groups counts by the structure of their **instantiated** bounds, alpha-renames bound keys, and converts 0/1 conditional bodies to Boolean formulas. Each truth-table row is a Venn region, each column an existing count. Exact integer elimination over the columns (including the universe column) yields linear identities, emitted in **both** directions. It also proposes pointwise subset inequalities, count-at-most-universe, and shared-member witnesses for two counts.
- `proposeCountPicks(counts, valueOf, options)` scans a bounded concrete model and proposes the existing distinct-key lower-bound rule when positive cells already exceed a count's assigned value. Returns `{picks, audit}`; no numeric answer from the callback becomes an axiom.

Default budgets: 8 Boolean atoms per bound group, 64 counts, 256 fact instances; concrete scan up to 256 cells per count, 32 keys per pick. Oversized/non-Boolean counts are reported as skipped, not interpreted as empty sets. These are opt-in proposal limits, not changes to the prover's clocks. `regions.rows` is an internal search representation; **no undeclared region variable may be appended to a certificate**. The rows overapproximate arithmetic predicates as independent Booleans. Infeasible rows may lose proposals, never justify stronger ones.

The generated `CountInst` is a disjunction: the sum inequality **or a counterexample key**. Even a provably false inequality can be a sound proposal when its witness branch is possible. Never append the sum inequality alone to a goal. Call `mcGoal`/`countedGoal`, prove the result, and submit the actual certificate to `checkMC`/`checkCounted` (or the counted-machine checker). A failed/unfinished search is not a proof.

## Q3 integration

At the end of `certFor`, once `named` reads exist, retain the current proposal pool and add:

```ts
import {countsForReads, proposeCountFacts, proposeCountPicks} from './count-facts.ts'

const cs = countsForReads(decls, named)
if (cs) {
  const extra = proposeCountFacts(cs, [goal, decls, named, insts], {reserved})
  insts.push(...extra.insts)
  wits.push(...extra.insts.map(i => i.wit))
}
```

Preserve the returned witnesses when building quantified law/flag instances. Reserve the machine's names, all existing read/witness names, and the whole existing certificate. Do not let `wide`'s current `splice(10)` erase the new proposals: put them in the retained lazy pool, or run this after truncating the old pool. Do not change the final checking path.

After a validated model arrives, use the caller's numeric evaluator over its concrete cells (missing cells at the **same defaults as model validation**) as `valueOf`. Append new `proposeCountPicks(cs, valueOf).picks` to the certificate's existing picks, deduplicating by count read and key list. Rebuild with `mcGoal`, re-run the model search, and carry the picks in the eventual certificate. Rebuild read names consistently across MBQI rounds; never reuse a pick against a different read. The test-only evaluator in `core/fixtures/count-facts.ts` is an example, not a production dependency.

The Q3 archive `runs/q3c-candidate.patch` contains a narrow partition detector; replace that detector with this call, not the surrounding certificate validation. The current `core/counts.ts` in this branch is intentionally untouched.

## Tests / evidence

`bun test core/count-facts.test.ts kernel/count.test.ts kernel/countmachine.test.ts` (run on boat). `scripts/test-shards.ts` registers the new suite. It checks kernel-accepted partition/inclusion-exclusion/complement/three-set identities, subset facts, machine-read instantiation, empty/oversized/unsupported inputs, witness freshness, bounded and dishonest model callbacks, tampered picks, and frozen model elimination. Archived inputs, measured models and SHA-256 manifest: `kernel/fixtures/count-facts/`. Full measurements, limitations and proposed future Lean statements: `runs/REPORT.md`.
