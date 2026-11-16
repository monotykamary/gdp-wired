# Shape-derived typed bound substitution

`tryTypedBoundSubstitution({id, bundle, providedSourceAST, options})` accepts a
caller-validated structural bundle (`original`, complete `proof` provenance,
`verdict`; no capsule schema/identity rewrite) after one term-prelude restore.
It returns `null` for non-candidates; an identified candidate with an ambiguous
or unsupported shape throws. Output is **EMITTED_NOT_CHECKED**, never acceptance.

The supported shape is a unique complete usual producer under projection /
inference and one explicit Skolem context, with independent finite-domain
parameters supplied by bounded source comparisons. Map coordinates, witness
values, quantified flags, and law-local variables are inferred by constraints;
name spelling, relation metadata, protocol identifiers and certificate entry
numbers do not select an algorithm. Different bound scopes can reuse names.
Ambiguous coordinates, mixed domains, counted/history/sum/function extensions,
row updates, ordinary public laws and universal-binder relabeling currently
refuse this route. Existential binder relabeling uses a checked substitution
against the actual supplied public body; the supplied AST is never rewritten.
Boolean associativity is normalized only for syntactic preflight.

The current retained emitter regenerates the **entire** producer certificate,
including all helper laws. The Lean program annotates its tables/trees and tests
cache choices against complete reconstructed start/step goals, with no
hardcoded cache index list. Final acceptance requires `checkSMachine`, option
completeness, preserved tree shape, source alpha validity, ghost validity,
operational inclusion, and each original public existential statement. All
these declarations are included in `requiredTheorems`; a single public law
also has a generic `${id}_source` compatibility alias.

## Canonical generic helper

`lean-kernel/TypedSource.lean` (promoted and owned by the parent) imports only `SourceInclusion` and `BoundGhost`. Its theorem
`Kern.TypedSource.ex_of_holds` derives the original public existential body from
a semantic law on a ghost extension. It is independent of certificate layout,
parameter count, maps and names. It introduces no axioms.

## Checks

All checks run remotely with `supercomputer`; no local Lean/build/test runs.
`roles.test.ts` covers independent domains, inconsistent swaps, unclassified
coordinates and reused law-local names. `TypedControls.lean` includes a concrete
unequal-domain counterexample to treating a role swap as equivalent.
`remote-test.ts` is TEST ONLY: it can construct the current source fixture or
read `TYPED_SOURCE`. It loads one complete retained capsule, restores once,
emits through the product API, and hands the project to Lean. The production
API imports no protocol registry and needs no retained Lean source file.

The first tests exposed Boolean association and captured-versus-producer
quantified-binder differences, both now handled structurally. Frozen check 05
compiled the complete typed family, actual supplied source theorem and helper
with only standard axioms; TypeScript also passed. Its overall Lake run failed
on an unrelated old/current counted-library overlay, so that run is not a
whole-project acceptance. The production factory is now `liftProject`, and the
promoted `TypedSource` is taken from the complete product `leanLibrary`, not read
from this directory at runtime. The subsequent public CLI check passed: `runs/public-06/typed-public.files/
project/LIFT-CHECKED.json` records `SOURCE_CHECKED`, 20 audited declarations,
`p3_family` and `bapa_client_server_db_ae_source`, and successful native `lake
build` / root recheck. Only the standard axioms occur. The post-acceptance
extra control runner initially stopped at a test-only `DecidableEq Row` issue;
its row equality now uses `rfl`. The authorized controls-only check then
compiled all six controls, including full-checker rejection of inconsistent
roles and preservation of all 27 entries. See `runs/controls-07/typed-controls-
only.files/{typed-controls.log,full-role-control.log,controls/ControlOrigin.json}`.
That job failed only in its final audit wrapper because unqualified `#print`
requests were compared to qualified Lean output; the requests are now fully
qualified. No additional source-proof or capsule replay was performed.
