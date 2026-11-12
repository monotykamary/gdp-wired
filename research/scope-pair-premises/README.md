# Scope extraction: premises for used equal-key rows

Implementation child of exact `9eb09b8326fc2670fad6725f774ab1b252c4d343` on `k/scope-pair-premises-9eb`. Implements item 3 of Fable §51.5, commit `cbe9f611acf54f938118277498acff9d9dfc5fa2`. **Source packet only. No compiler, imports, tests or measurement job has run.** Existing sizing/grid packets and their holds are unrelated and unchanged.

## Hypothesis and limits

At a fixed native leaf path, `leafRows` creates equal-key rows from all map-cell names in initial path/fact rows. `usedHyps` reports direct fact citations (and product ancestry), but not facts whose only contribution is a cell name needed by a cited pair row. Removing those facts can therefore remove an input row required by exact transport. This is a source-level mechanism, not a diagnosis proven for T301 or R4.

The proposed fix changes **scope capture only**: `scopeCountProof` calls new `countedScopeHyps`, not the old fact-only helper. Kernel, checker, exact transporter, closure planner and `rescopeCountProof` are byte-identical to 9eb. The legacy `countedCertificateHyps` function and its separate legacy caller in `counts.ts` are unchanged.

`IMPLEMENTATION.patch` is a zero-context patch (use `git apply --unidiff-zero` against exact 9eb); the complete source is alongside it.

## Algorithm

1. Retain every index returned by the existing `countedCertificateHyps`, including whole independent lemma source slices. Never replace that set with a smaller one.
2. Walk the original main tree. At each leaf, construct the actual native `framePath` (linear, mono, frame and lemma prefixes) and its unchanged `leafConstraints` rows. No solver or checker invocation is added to extraction.
3. From **only initial atom/fact rows**, record the pre-pair cells. Every fact-row owner of each cell is a supplier, including zero-valued stored coefficients. Atoms supply cells without adding a hypothesis. Pair/term/naturality rows do not invent an initial supplier.
4. Follow every input step and recursively every cited product operand, accounting for square offsets. Also retain dependencies of explicit product operands that the current transporter reindexes even if not cited by the final arithmetic.
5. Add direct fact origins on this actual path. For every reached pair row, add **all** fact suppliers of both cells. Duplicate suppliers are deliberately retained, not minimized.
6. Existing formula-to-law attribution in `scopeCountProof` names all corresponding laws, preserving family order and duplicate-formula conservatism. Existing declared-premise checks remain strict: a contradictory explicit declaration is refused, not silently repaired.

New loops use existing `checkWall`/`startWork` and `visitLinearCells`. Native row rebuilding has its existing charged cost. The extra extraction is not free, cached, calibrated or demonstrated to fit a production budget. A hard budget stop propagates; no catch-and-search, fresh headroom or fallback is added.

## Soundness argument (conditional, not a full transport theorem)

Let H be a source goal and P one fixed native leaf path. Let F(h,P) be the initial fact rows emitted for h, and A(P) the atom rows. The pair loop uses exactly the cell names in A(P) union all F(h,P), before term closure. Consider a reached pair row with cells a,b.

For each cell occurring in a fact row, the collector retains every owning h. If it occurs only in an atom row, P itself retains it. Therefore after deleting hypotheses outside the collected set, both a and b still occur in the initial name set. The map names, parsed keys and P are unchanged, so the same native `sameKey` test is true and both orientations of that pair row are generated again. Row indices may move; the existing exact transporter handles indices and must still succeed and pass the unchanged checker.

The output is explicitly the union with the old reference set. Thus for successfully extracted ordinary valid metadata, old hypothesis dependencies are a subset of new dependencies. The existing formula matching maps this to a superset of law premises. Declared scopes omitting a newly required premise can now be refused; they never acquire a false checked receipt. Existing independent lemma slices are retained wholesale, so their local pair suppliers remain present without new lemma-tree analysis. Auxiliary mono/linear proofs are over their own goals, not parent hypothesis arrays.

This proves preservation of **the identified fixed-path pair-row availability**, not completeness of every dependency mechanism or every transport. Used naturality/term rows, model/count-declaration changes, opaque metadata, changed paths, missing held suppliers, or other transporter limitations can still cause a decline. The new helper does not grant a checked verdict. A result is accepted only through the original replay/check path, and a missing row still fails closed. No theorem, law, machine or conclusion is weakened.

## Prepared regression tests (UNRUN)

`core/count-scope-hyps.test.ts` constructs native row-indexed proofs without solver search:

- a used pair row whose M[j] supplier fact is uncited (old refs [0], new [0,1]); exact old reduced-goal transport declines while retaining the supplier permits exact transport;
- a generated but unread pair does not retain its otherwise-unused supplier;
- duplicate cell suppliers are all retained;
- products-of-products and square offsets preserve supplier ancestry;
- frame-prefixed input indices use the actual native path.

These are synthetic source regressions, **not substitutes for T301 or R4**. They have not been executed. Existing scope, rescope and transport suites are required in the sealed comparison spec.

## Real-case comparison and current blocker

`COMPARISON-SPEC.json` describes fresh old/new processes, the frozen 9eb scope module `reference/count-proof-scope.ts.txt` (data, not an executable import), unchanged checkers, exact input identity, native prechecks, canonical T301 replay, and fixed-context R4 closing transport. It distinguishes IMPROVED, SAME_DECLINE and REGRESSION; a false-to-false result is not a fix. The same original closing context may correctly decline sooner if new dependencies identify an absent law. No widening/retry of the production closing algorithm is implemented here.

**Exact real-case payloads are required before any claim.** R4's owner confirms the timed artifact exported no held proofs, source contexts or failing member. Its public model/laws and 17-law name order are not the captured closing machine/scoped payload. T301's owner likewise confirms that only reference laws/machine and scope metadata survived; runtime instances, certificates, source goals and exact failing replay arguments are missing. Missing data means BLOCKED_MISSING_REPLAY_INPUT, never a synthetic stand-in or a passing comparison. See `INPUT-STATUS.json`.

A fresh full search/capture, changed family, guessed source context or new runtime admission requires separate authority. This packet does not authorize any of those. No success for Inv* or R4 is claimed.
