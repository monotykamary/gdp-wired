# Inferred families and local binder alpha transport

The public source and retained producer are compared as complete machines.
JavaScript proposes local binder renames; Lean checks freshness, semantic
transport, and the whole resulting machine equality. The complete retained
helper family is checked and supplies every selected public law.

Two different scopes occur:

- `QAlpha`: quantified-flag keys and their bound occurrences.
- `RowAlpha`: a pointwise map update's `each` key and its bound occurrences.

The source-to-producer chain applies `QAlpha` first, then `RowAlpha`. It never
rewrites the retained proof or source law. Changes outside those scopes cause
the whole-machine equality check to fail. Both transports support ordinary and
counted reachability; counted source declarations remain unchanged.

## Observed differences, before proof

Read-only inspection batches `20261115-201732-zlb4e8` (first case) and
`20261115-202218-6o69oz` (remaining cases, fresh processes) found:

| Case | Public entries | Flag binders | Row binders |
| --- | --- | --- | --- |
| `twophase` | 2 | `allPrepared` | none |
| `two_phase_commit` | 8 | `noGo`, `allYes` | `GoCommit`, `GoAbort` |
| `learning_switch` | 0,1,2 | `noRoute` | `T`, `P` |
| `learning_switch_i4` | 0,1,2 | `total`, `linked`, `below2` | `Link`, `LinkSet`, `T`, `Pend` |

All observed changed paths were binder declarations or corresponding variable
occurrences. Inspection alone does not establish alpha equivalence.

The counted cases `consensus_forall` and `consensus_wo_decide` also need the
`VotingQuorum` row binder: respectively `k$4` to `k$24` and `k$3` to `k$19`.
Their previous failures were at the final source-shape equality, not at the
quantified-flag validity check.

## Controls

`inferred-alpha-control.ts` isolates the two obligations. The capture control
constructs a target definitionally equal to the syntactically renamed source,
then requires Lean to prove `QAlpha.validAll = false`. Thus unrelated machine
inequality cannot explain rejection. The body-drift control independently
checks alpha validity, and accepts a failing build only if its sole error is
at the intended whole-machine equality line.

## Checked evidence

All four inferred source projects and their full families passed Lean and axiom
gates in `20261115-205146-a9zrg8`. That batch stopped only at an off-by-one in
the negative-control harness; the positive source logs remain valid.
`20261115-210410-xwd8xm` passed the corrected isolated controls, types,
9 tests / 25 assertions, and commitlint. The row capture counterexample also
checks that omitting freshness can change an actual update from 1 to 0.

`20261115-204348-11vcsk` passed complete counted source checks for
`consensus_forall`, `consensus_wo_decide`, and the no-row regression
`toy_consensus`, plus types and 6 tests / 25 assertions. Their checked receipts
are in `runs/bapa-counted-row-02/counted-row-source-gate.files/<id>/`.

The generated library hash agrees across both independently executed gates.
RowAlpha is a separate module; the frozen QAlpha compatibility sources are
unchanged. These are proofs of the emitted public source laws as encoded,
not a blanket 29/29 or external source-language correspondence claim.
