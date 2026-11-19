# Native aggregate proof evidence

`proveRule` can prove a single requested invariant via a finite-prefix certificate or a ghost-write certificate. It uses the original machine snapshot, before automatic lazily declared sums, and declines this route when `withSumsOf` extends the rule. Explicit deterministic work mode, `from: 'any'`, and `search: false` also keep their existing routes. The optional aggregate stage has at most half of the requested search time, capped at 30 seconds, under the caller's existing wall. A failed proposal or unproved companion kind falls back to normal proof search.

When the result is checked this way, the `proofOutput.on` event retains an `aggregate` proof node (possibly under a `derived` wrapper). Its `machine`, `law`, `certificate`, and optional `kinds` materialize `LeanItem.aggregate` as follows, in the same process:

```ts
const {machine: source, law, certificate, kinds} = node
const file = toLean([{id: 'Exact', aggregate: {source, law, certificate, kinds}}])
```

`Exact.original_law` is the original source invariant. Any companion kind conjunctions are flattened at the same quantifier key and checked as an ordinary inductive family, exported as `Exact_kinds_laws`. The aggregate theorem assumes none of those kinds. `leanProject(file)` bundles the imports. A fresh-process replay must first restore the node's retained term interning snapshot in order. The radix simulation planner only supports a unique ordinary family, not aggregate certificates or mixed provenance; use this direct Lean route for aggregate nodes.

`focused.sh` checks each default-path proof and its required controls, emits Lean and elaborates it. `review-controls.mjs` exercises a broken companion kind and a law that introduces an automatic sum. `paired.sh` runs cold stock/candidate processes on the same VM under pinned Node; `review-roster.mjs` identifies rows the aggregate search could affect.
