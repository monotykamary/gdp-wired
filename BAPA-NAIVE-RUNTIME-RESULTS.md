# Original-Ivy naive consensus: concrete runtime conformance

For the 0.49.1 continuation only. Release 0.49.0 remains the frozen slices-1/2 source `142d1f5ab`; its commit/tree and consumed cohort were not moved, rebased or rerun.

## Verified gate

Batch **`20261114-092524-36xsij`**, `naive-runtime-conformance`: **28 tests pass, 0 fail, 13,699 assertions**, strict TypeScript, type-aware lint (0 warnings/errors), commitlint. Native strict-once close reports cleanup complete, admission closed, journals retained; no pending/unlaunched items. Evidence root:

`runs/bapa-naive-runtime-03-fetch/naive-runtime-conformance.files/`

Rows SHA256: `0555717389f7663d4eb4d689a72a7cd14717b1919c3307e1ed105a2d16219ef7`.

## New controls

`research/bapa/rigid-naive-runtime.test.ts` uses an independent array-and-loop source interpreter: no C/E condition constructors, machine evaluator, tuple encoding, lowered fact, ghost or generated witness in its state-transition logic.

- Exhausts **29 reachable states** of one validated 2-node/2-quorum/2-value interpretation. All **108 requests per state**, including invalid action/index sentinels, give **3,132 checked state/request pairs**. The log's `transitions` counter includes refused requests; it is not an enabled-edge count.
- Compares both interpreter and compiled-JS enabledness and every observable `vote(Node,Value)`, `decide(Quorum,Value)` and `decision(Value)` cell after each enabled step. Disabled actions must throw in both runtimes, not silently stutter. Compiled BFS branches use `fork` because compiled `step` consumes its input state.
- Checks a genuine non-majority intersecting family `{0,1}`, `{0,2}` on four nodes, preserving the quorum coordinate in the two distinct `decide` cells.
- Exercises node/value coordinates 64 and 65, duplicate-extension quorum names and the deterministic smallest intersection witness.
- Covers empty Quorum/Node domains and empty Value; inhabited Quorum with no Node is rejected, not assumed away.
- Retains a disjoint-quorum bad source trace (the normal validated API refuses its instance), a missing-no-prior-vote-guard bad trace in both runtimes, and a changing-membership trace showing why the interpretation must be fixed for the whole run even when each individual table intersects.
- Checks the three given helper properties on all explored valid concrete states. The source state contains no `learnedQuorum` ghost map and no counting machinery.

The 21 existing validator/lowering tests also pass unchanged.

## Retained harness failures

- `20261114-092402-im9913`: the new test incorrectly passed the compiled runner to `allowed`, whose contract requires `interpret().queries`. Strict typing and runtime both caught the misuse. No implementation mismatch established.
- `20261114-092447-wb1wqq`: the test then incorrectly treated disabled actions as stutters and reused the compiled state across BFS branches. It also referenced nonexistent `Machine.queries`. Corrected only the fixture: compile the real flags/assumption, assert rejected actions, fork compiled states, and exclude actual history/least-query machines from this simple adapter. No production change was needed.

Both failed outputs remain in their numbered fetch directories.

## Explicit non-claims

This is finite testing, **not** a symbolic-size theorem, proof certificate, ghost elimination, source-wrapper export, completeness result, or release acceptance. The original intersection axiom is ASSUMED here; the old suite's majority port proves intersection by counting. Helpers are still GIVEN, not found.

The opt-in untrusted strategy and its caps are unchanged. The next proof attempt remains pending Fable's reading of `BAPA-FABLE-PROGRESS-REQUEST.md`; no speculative full-port retry was made. D's diff review remains required before merge or counted use.
