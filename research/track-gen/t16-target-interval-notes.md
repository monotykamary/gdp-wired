# T16 interval post-target refinement

## Falsifiable hypothesis

The checked shared circuit reaches enumeration but does not reach the fifth
named drop. Its completed original-family first rounds report 4,231 request
prunes and no state-prefix prunes. Requiring every dependency of an atom to be
exact may be unnecessarily weak for counts and arithmetic. Conservative ranges
could rule out target failure earlier without losing a concrete transition.

## Semantics and trust boundary

This is opt-in `postTargetIntervals` under `postTargetPruning`, not a production
change. A slot is exact only at its existing per-operation source readiness;
before that, its declared finite/global range encloses every possible value.
Constants are singleton ranges. Addition, truncated subtraction, natural
multiplication, minimum and maximum propagate enclosing ranges. A conditional
selects a branch only when its predicate is definitely true/false; otherwise it
joins both ranges. Other supported terms retain their existing enclosing global
bounds. Non-natural intervals fall back rather than applying natural formulas.

Predicate truth is -1 (definitely false), 0 (unknown), or 1 (definitely true).
Inequalities require separated interval endpoints; equality is true only for
identical singleton ranges, false only for disjoint ranges. Overlap stays
unknown. Negation, conjunction and disjunction use conservative three-valued
logic. Only truth 1 for the target permits pruning its negated postcondition.
By induction on this DAG, a concrete failure cannot be pruned: its concrete
values are inside the propagated ranges, so its target cannot be definitely
true. This is an argument to test, not a checked universal proof.

Keep the 65,536-character native-body cap. An unsupported or oversize interval
screen falls back to the checked readiness screen, incrementing a diagnostic
counter. Wall expiration still propagates. Independent full-family/source-step
certification remains the only authority to remove a law. No bound, candidate,
transition dispatch, domain or wall is enlarged and no source names are used.

## Validation required before any interval pilot

- Compare no post-pruning, readiness pruning and interval pruning against the
  source interpreter on the complete existing finite binary/ternary cases.
- Add arithmetic, polarity, unknown conditional branches, and three-cell count
  coverage. Require fewer nodes for the monotone zero-write count example.
- Force a native-cap fallback and require identical complete concrete results.
- Preserve independent callback/facts/unsupported/wall tests and all core tests.
- Run full TypeScript, type-aware lint and the proposed commit message check.

The hash-bound `runs/t16-target-interval-overlay/` is now undergoing those checks
on submission-class boat. This document does not claim that they passed.
