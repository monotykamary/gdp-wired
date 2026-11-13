# Section58: required-only closing reduction

Main t6 assigns section58.8 to B in a child of rollback17a5b773. This child is `track-m/required-reduction`; the running rollback7w03u3 source/worktree and collector are untouched. Source basis: section58 at1a9a2d7a3 and correction58.11 atfff710de2. No kernel, final finish, work allocator, controller state machine, production flags, writer, peak exporter or snapshot-schema change.

## Implementation

- `core/count-proof-scope.ts`: only remove a candidate's instance entry when it is absent from the target family. `scoped.unused` is a candidate-law namespace; ordinary fact and quantified-flag keys remain. Retained family-law instance names join the recorded premises returned to finish. Order follows the target family.
- Compare complete expanded source/target goals **and native declarations** using the existing metered ordinary-data stamp. Only equal pairs bypass transport and retain the original certificate object. Equality does not create proof authority: `checkMC` runs even if closing deferral was requested, and unchanged final family checking still runs. A checked-reduced receipt is minted only after native checks and context checks succeed; deferred output stays unchecked.
- On an actual leaf-mapping refusal, match `detail.sourceFact` against the original source family's instantiated law formulas. Only absent, positively matching law owners are named. An equivalent retained owner prevents that attribution. Generated pair/term/naturality/marker rows without a source fact remain UNATTRIBUTED; cut-validation, deadline, malformed-data and native-check failures are never promoted to law blockers.
- Ownership resolution happens outside the observational transport callback, so an authenticated budget exception cannot be swallowed by that callback's diagnostic catch.
- `core/counts.ts`: choose the greatest existing closed held family on the first closing invocation; no speculative smaller-family retry. Remove production closing's supplier-repair callbacks and shared-bit fallback. The generic controller and supplier helpers remain unchanged for other uses/tests. Return named outside-family BLOCKER information to the controller and observer; final target membership and finish authority are unchanged. Returned proof premises, rather than stale selected-row premises, reach finish.

## Written, NOT RUN

New small native tests cover held instance preservation, real fact/flag namespace preservation, native certificate identity, declaration mismatch preventing the shortcut, corrupted unchanged certificate rejection under requested deferral, actual source-fact blocker attribution despite incomplete untrusted premise metadata, and non-attribution of generated/cut/deadline failures. Existing scope-diagnostic tests now force non-identical goals where transport itself is tested. Existing production acceptance tests expect greatest-family-first/no supplier repair, while genuine transport/collection hard-stop tests withhold optional equality evidence to continue exercising those paths.

One focused boat gate plus one strict compiler invocation is authorized, not yet admitted. Separate test processes will isolate module mocks. No local test/compiler/prover run. D narrow source/packet review precedes gate launch; no retry implied by this plan.

## Pending replay

If the running rollback measurement exports a complete snapshot, this is the first requested behavioral variant to replay. It must be combined with the independently green closing-only harness, preserve the original captured17a5 identity/source metadata, bind the changed execution source separately, and pass D's exact packet review. No snapshot is assumed present, no replay has been started, and neither synthetic tests nor source inspection prove real-run fidelity.

## Source findings

Kernel assumed() includes every unquantified family law and only supplied quantified instances. For fixed machine/owner/non-law instance keys, given(), closing() and native declarations do not depend on family membership. Recipe capture starts with the full set, but a successful canonical rescope returns a reduced-source payload; therefore not every held payload retains all44 candidates. R4 event counts/original-stage costs were not re-read for this change; original-stage units are a baseline, never an upper bound. These match section58.11.
