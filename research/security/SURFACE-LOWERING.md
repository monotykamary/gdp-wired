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

A deliberately corrupted lowered law drops the existential body and replaces it with a universally quantified tautology. The bounded oracle finds a concrete disagreement, while `proveLaws` proves the mutated tautology. This demonstrates why proof success for the lowered formula alone is insufficient.

## Boundary

This is finite regression testing, **not a universal equivalence theorem**. The interpreter only implements the operators used by these fixtures (natural arithmetic, map reads, conditionals, and universal binders); it does not cover flags, finite sorts, projections, all DSL constructs, arbitrary domains, kernel/Lean semantics, or source-policy parsing. Kernel and Lean gates retain their own responsibilities.

The quick CI roster invokes this test, and `supercomputer/suite.json` has the matching interactive remote job. Run the focused remote check with the lane job file/command recorded in the lane receipt.
