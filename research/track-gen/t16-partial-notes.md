# Unready-atom shortcut: static review and pending measurements

Implementation checkpoint: `32772de6`. Not promoted. No remote test has
executed for this change; the upload failures are recorded in `runs/REPORT.md`.
The coordinator's submission hold remains in force; no retry is scheduled here.

## Falsifiable hypothesis

In `Compiler.compile`, an atomic predicate with an unassigned dependency
already returns true (unknown in this pruning screen), independently of its
polarity. Previously, the generated function computed every prerequisite
term using readiness-dependent zero placeholders before returning that same
unknown value. Avoiding those computations should reduce enumeration work
without changing any proposed finite predecessor/request pair.

The new guard uses the maximum assignment rank of the atom's dependencies.
Before that rank, it returns the same unknown. At and after that rank, every
prerequisite term's dependency is assigned, so the old per-term placeholders
were inactive and the unguarded DAG computes the same expression. Dependencies
of conditional terms include the condition and both branches. For request
screens, state slots have rank -1 and are already assigned; this remains true.
Logical conjunction/disjunction and polarity recursion are unchanged.

This is a code-review argument about an untrusted finite screen, not a Lean
proof or a claim that its finite scope covers all states. Main's independent
family/precondition/facts/source-interpreter checks remain the drop authority.
No source law, proof budget, search domain, cutoff, or production switch changed.
The 64-KiB generated body cap now includes the early guard's bytes.

## Regressions awaiting boat

- Compare every proposed ternary predecessor against independent interpreter
  truth for equality, negation, inequality, nested disjunction/conjunction,
  and a conditional arithmetic term. Reject proposals deliberately so every
  candidate can be compared, not merely the first one.
- Enumerate all bounded request pairs under a conditional-term assumption,
  checking that neither partial placeholders nor a polarity change reject a
  legitimate request prematurely.
- Existing cancellation, caller-protection, unsupported-fact, dependency,
  native-row and whole-family tests remain required.

## Measurement and rejection conditions

Collect all six unchanged resumed checkpoint probes first. Preserve their
actual failures, exits, placement and active wall. Then collect the same six
probes for the shortcut. Do not treat the old cancelled batch or launcher
process durations as algorithm wall.

Require at least five NEW named-seven drops in **each original-40 run**, all
three repeats, with every active wall at most 2,000 ms and every job exit 0.
The survivor-34 runs have already replayed the historical CV-bound removal;
report their new drops and historical-plus-new counts separately. Do not
require five new survivor drops or silently credit historical drops to the
original-40 experiment. The replay summary reports original-three success,
all-six exits and all-six walls separately, not an authoritative gate.

If the criterion fails, leave production disabled and retain the falsifier.
Only after it passes should the strict original harness and the other-28
list/proof guardrails run. Final admission still belongs to lane D.

## Immutable retries once the coordinator permits submission

The prepared `/tmp/gdp-lane-a-frozen.uLpIQc/checkpoint` clone is pinned to
`bef4020f`, and `/tmp/gdp-lane-a-frozen.uLpIQc/wip` to `32772de6`; both include
exact submodule checkouts. The copied data file has the expected SHA-256.
Do not edit these clones during upload. The WIP clone predates this note and
the replay-summary clarification: it is sufficient to test the core shortcut,
not to validate later changes to the replay diagnostic. Clone the new lane tip
separately when validating that diagnostic. No ignored logs or cache cleanup is
necessary to fix an upload race.
