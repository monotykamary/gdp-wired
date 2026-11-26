# General prover gap: rigid-function axiom instantiation

2026-11-14. Historical proposal for Fable/D review. Main subsequently authorized a narrow opt-in/default-OFF implementation on `after/bapa`; see `research/bapa/notes/BAPA-FUNCTION-INSTANTIATION.md` for current results. The proposal and original failed search below are retained unchanged as history.

## Reproducer and evidence

`research/bapa/rigid-minimal.ts` supplies the original intersection axiom as a universal function fact and asks only `quorums > 0 -> nodes > 0`. No state helper or existential appears in the law. Batch `20261114-055659-gafj9t` returned `proven=false, checked=false`, with the local candidate `nodes=0, quorums=1`. That is not a valid full interpretation of the original axiom; it shows incomplete instantiation, not a counterexample to the source theorem.

`kernel/prove.ts` `instancesFor` calls `withFacts(m, inst, fnKeys(m, build(inst)))`. A scalar-only goal initially contains no function reads, and the multi-key axiom therefore receives no instance. The current `opts.seed` seeds laws/flags, not these multi-key function facts. The semantically sufficient tuple `(0,0)` is never proposed.

A manually supplied ground instance is a **GIVEN hand seed, not found**. The diagnostic `rigidMinimalGivenZero()` names it `GIVEN intersection instance at (0,0)`. It is not a state-helper invariant, but it is still supplied proof-search assistance. The generic `lowerRigid()` does **not** add it. No port may count this as automatic discovery or silently inherit per-port seeds. A source-level Lean wrapper must prove that even this redundant ground fact follows from the original universal axiom.

## Proposed general fix (review before implementation)

Extend only the untrusted function-fact instantiation strategy. Read patterns from fact bodies, preserving function head, arity, complete tuples and repeated-variable agreement; use a covering pattern set where no one read covers every binder. Derive a fact binder's sort from its domain guard and argument/result sorts from the existing rigid declarations. Ground here means free of that fact's own quantified binders: scoped law keys, request inputs and existing witnesses may remain free in an ordinary instance.

Per sort S, propose candidates in this reviewed order: (1) argument tuples of actual rigid/function reads in current goals, by matching; (2) other scope-valid terms of S already in the goals, including reads of maps with declared value sort S; (3) results of rigid functions into S applied to candidates found; (4) the sort's least natural representative, zero, last. D explicitly confirmed this declaration-derived candidate is admissible even when absent syntactically, with every original per-variable range antecedent retained. **Bootstrap from the sort, not a literal occurring in this law.** Zero is not an assertion that the sort is inhabited: every instantiated axiom retains `0 < size` in its domain guard, including empty sorts. No port-specific term list or new fact is permitted.

Check the sort-dependency graph of rigid functions. Acyclic signatures bound the typed term closure; cyclic signatures use an explicit reported depth limit and can return not proven. Bound/deduplicate candidates and Cartesian tuples before materialization, with charged search limits and a per-fact cap filled in the order above. Preserve off-diagonal tuples and full-arity matches. Feed only ordinary `Instances` through the existing obligation construction, kernel `checkLaws`, and Lean exporter. Limit exhaustion is not proven, never finite completeness or a valid semantic counterexample.

The deciding-quorum ghost map's **value sort is Quorum**. Its reads must be eligible quorum candidates when the agreement goal mentions them; this is proof-side type metadata, not an observable model map or a new trusted fact. The minimal example does not exercise this and cannot stand in for its control.

Fable's design review: SECTION-75.7 at design commit `c0113bf81`, with sort-derived bootstrap, typed ordered candidates, graph/depth limits and the controls below. D accepted the **design boundary only** in `BAPA-GENERAL-INSTANTIATION-DESIGN-REVIEW.md`: opt-in/default-off, charged bounded discovery, no new facts or trusted rule. The non-rigid path must remain byte-identical. This is **not shared-prover implementation, merge or count-change authority**. No shared `kernel/prove.ts` edit or canonical-count change is made here; integration waits for explicit authority/review.

## Required controls

- The unseeded minimal machine closes with the strategy, with no new `m.facts` entry and no GIVEN instance.
- The equivalent minimal law `1 <= quorums -> 1 <= nodes`, with no literal zero, also closes from declaration-derived bootstrap.
- A triggered two-argument fact binds both arguments; off-diagonal and three-argument tuples, repeated variables, covering pattern sets and no-match cases preserve identity, arity and scope.
- A cyclic rigid signature stops at its declared depth limit and reports not proven rather than silently claiming closure.
- A separate proof-side map control discovers quorum candidates from `learnedQuorum(value)` results; it is not satisfied by a scalar/constant-only test.
- Axiom omission, missing range and missing membership conjunct controls remain unproven/refuted as appropriate.
- The actual exported proof checks in the unchanged Lean kernel, and its public source theorem discharges the original axiom rather than a privileged chosen table.
- Existing finite, tuple, function and ghost-map regressions remain unchanged. Any counted canonical comparison needs its own fresh explicit authority; the ongoing slices-1/2 cohort must not be touched.

The current minimal export is a diagnostic GIVEN-seed control only. It is not completion of the automatic minimal gate or the naive-consensus port.
