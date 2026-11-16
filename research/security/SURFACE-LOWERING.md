# Surface/lowering semantics gate

`research/security/surface-lowering.test.ts` is a CI control for the class of bugs where a law is proved only **after** a faulty binder/lowering transformation. It is intentionally separate from kernel proof checking: it evaluates the surface `Cond` and the emitted `Law` with a small local interpreter and compares their truth values.

## Checked scope

For each accepted fixture, the test enumerates the natural domain `{0,1,2}`, every `A[0..2]` valuation, and each named free-variable valuation. It checks:

- a universal map law;
- existential/universal alternation (`exists x. forall k`);
- an `int` existential's paired `x`/`x$neg` aliases;
- a free identifier that has a historical generated-binder spelling (`key$1`), ensuring the lowered binder does not capture it;
- labels that resemble generated names, which must remain labels; and
- duplicate policy labels, rejected by this gate's fixture admission before a comparison could accidentally select one.

The nested `everyKey` fixture is a structural negative control: the public DSL must refuse it as a two-key law rather than silently lower it. It has no accepted lowered counterpart by design.

A binder-capture mutant deliberately binds the free `key$1` parameter; the oracle rejects it on an explicit valuation. A separate lexical-scope control keeps a free occurrence outside a same-named inner binder free.

A deliberately corrupted lowered law drops the existential body and replaces it with a universally quantified tautology. The bounded oracle finds a concrete disagreement, while `proveLaws` proves the mutated tautology. This demonstrates why proof success for the lowered formula alone is insufficient.

## Boundary

This is finite regression testing, **not a universal equivalence theorem**. It compares the raw `Cond` captured before law lowering with the lowered `Law`; a bug in `Cond` construction that corrupts both representations identically is outside this oracle. The duplicate-label control validates fixture admission, not the production source-policy parser (covered by its separate policy-identity tests). The interpreter only implements the operators used by these fixtures (natural arithmetic, map reads, conditionals, and universal binders); it does not cover flags, finite sorts, projections, all DSL constructs, arbitrary domains, kernel/Lean semantics, or source-policy parsing. Kernel and Lean gates retain their own responsibilities.

The quick CI roster invokes this test, and `supercomputer/suite.json` has the matching interactive remote job. Run the focused remote check with the lane job file/command recorded in the lane receipt.


## Ordered-list source boundary

The ordered FIFO extension starts **before** a `Cond` exists. It writes a small Python FIFO (`self.items: list[int]`, `put` appends, `take` calls `pop(0)`), runs `extractPython`, and passes the public text law through `buildLaw`. The fixed reader must reject each unsupported scalar quantifier before any `StepLaw` is emitted. A separate concrete evaluator and positional mutants expose the value/key disagreement over the same FIFO transitions. It does not construct a source `Cond` or a lowered `Law` from a shared expression.

The exact scalar bound is every sequence over values `{0,1,2}` at sizes `0`, `1`, `2`, and `3`: `1 + 3 + 9 + 27` lists, for each of membership, equality, and order. Consequently it includes all three-value permutations and repeated values. The source evaluator quantifies **values** from the old list, while the mutant evaluator quantifies numeric insertion keys and interprets `items.has`/`items.has'` maps without renumbering keys after removal. This is precisely the distinction needed for the FIFO witness `[2,1] -> [1]`.

A separate positional-substitution mutant writes the known bad shape explicitly: it uses list positions for both the post-membership query and the `<=` comparison. The independent source evaluator rejects that mutant at `[2,1] -> [1]`; this control prevents a vacuous oracle from accepting the positional interpretation.

Record cases use an `Item` class with no `__eq__`, so their source membership control is object identity: `[a,b] -> [b]` does not retain `a`, while `[a,a] -> [a]` does. Current Python extraction honestly refuses the `Item` append (`one object in two places`) instead of inventing an aliasing model. The gate asserts that refusal and does not fabricate a lowered record law. If support is later added, the explicit refusal must be replaced by a source-to-lowered comparison, not removed.

### Previous blind spot and limit

The earlier fixture set captured a DSL `Cond` inside `rule.law` and began its comparison at `Cond -> Law`. It could catch a lowering that changed that `Cond`, but could not see `core/laws.ts` bind a textual list item (`o` or `j`) to an ordered-list **position** while reading source text. The new path covers source text -> extractor metadata -> `buildLaw` and demands a typed refusal for scalar quantification. It also checks independent positional mutants for every generated predicate, including duplicate-value membership and value ordering.

This remains a finite regression control, not a formal equivalence theorem. It does not prove all list lengths, values, languages, list operations, source parser behavior outside this FIFO, arbitrary record lowering (the record-argument aliasing fixture is refused; separate fresh-record native controls remain supported), arbitrary Python equality methods, or kernel/Lean equivalence. The local interpreters implement only the AST operators exercised here; production source replay, kernel checking, and Lean gates remain separate obligations.
