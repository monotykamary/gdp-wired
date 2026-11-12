# Scope extraction: complete native generated-row supplier closure

Generalized successor of pair-only `85a2a97a04b85e8ef133a18ab2653f66bf91bb57`, on `k/scope-pair-premises-9eb`, rooted at exact `9eb09b8326fc2670fad6725f774ab1b252c4d343`. Main explicitly requested this generalization after D's uncited min-term counterexample. Kernel and checker are unchanged.

## Status and authority

The immutable pair-only 85a run passed all nine tests (0 failed/skipped, 36 assertions) and one focused strict compiler check under FULL on boat, batch `20261112-125618-tzfvkf`, with verified one-attempt cleanup. Receipt `runs/scope-pair-85a2a97a-once/K-TERMINAL.json`, SHA `7f3ff8db6ef94d09ee08829ef6928d62f303126724e0488581b98608086cc41e`. **That result is not a test result for this generalized successor.**

Main separately authorized the generalized successor's retained nine tests plus new control and compiler ONCE on boat. The combined timed packet belongs to B and still needs D review/GO. Historical exact certificate replay remains optional and blocked on unavailable payloads, not a prerequisite for the new timed experiment.

## Changed code

- `core/count-proof-scope.ts`: use conservative native hypothesis closure before existing formula-to-law attribution.
- `core/count-scope-hyps.ts`: preserve every legacy reference; track all initial atom/fact names and all fact owners, then propagate ownership through the native term-introduction graph. Used pair, term and naturality rows retain root provenance. Products retain their operands; squares are certificate-owned.
- `core/count-cert-transport.ts`: inherited R1 correction rethrows the original BudgetExpired/WallExpired from legacy extraction. Ordinary malformed metadata still declines. Its exact transport/replay function bodies are unchanged.

All kernel files, checker, exact transport algorithms, rescope, `counts.ts` and planner remain unchanged. The same 98 protected-file hashes apply. No diagnostic, fallback, family-widening or timing behavior from B is merged here.

## Native dependency model

At a fixed native path, the closed row-source union is atom, fact, pair, term, and nat. Initial atom/fact rows seed every nonconstant name; zero-valued stored entries still count. Each name retains **every** initial fact owner, including duplicates. Path/frame/lemma/mono/linear atoms create an available root without inventing a fact owner.

For each native term row with `src.term = t`, every nonconstant name `n` in its stored coefficients gets an introduction edge `n -> t`. This includes further term, map-cell, variable and monomial names. The collector walks those edges backwards from names required by used generated rows, taking the union of root owners. This is lazy transitive owner propagation, equivalent to the forward least fixed point but without repeatedly copying owner sets.

Dependencies are taken from the source tag, **not merely coefficients of the used row**: pair needs both initial cell roots; term needs its generating term even if its coefficient cancels; nat needs the name whose availability generated it. Every cited input and product ancestry is followed, with square offsets; explicit unused products that the transporter still reindexes retain their operands too. Unknown native row-source forms fail closed. All loops are charged/deadline checked; R1 errors propagate unchanged.

## Fixed-path preservation argument

Retaining a root fact owner preserves its fact rows at the same path; retaining all its duplicate suppliers is a conservative union. Atom roots survive with the fixed path. Induct over the native term-closure generation: if a term name is available, its same term rows are generated; each named output becomes available for subsequent closure. Walking all ancestor edges of a used term/nat name retains the root hypotheses that seed those chains. Cycles/self-edges terminate in the traversal's visited set and do not remove root owners.

Thus each used fact remains; each pair has its two initial cells; each used term has its generator; each nat has its full-closure name. Certificate squares do not require a hypothesis to exist, and products are preserved from preserved operands. The legacy reference set and independent lemma source slices are unioned unchanged. Existing formula matching then conservatively names family premises.

This establishes generated-row **availability** under unchanged fixed-path/source assumptions, not a complete transport theorem. Row indices can move; the existing exact transporter and native checker remain authoritative. Changed paths, instances, count declarations, explicit incompatible premise declarations, resource stops, or absent held suppliers can still decline. No checked verdict is minted by scope metadata.

## Controls and real-case boundary

The existing nine tests are retained. The tenth test builds D's exact H0 `x<0`, H1 `min(x,y)<=100` certificate using H0, generated `t-x<=0`, and `-t<=0`. It also tests an outer `min(t,z)` introducing the used inner term transitively. Both subcases require original native validity, old reduced-context transport decline, new retained supplier indices, exact new transport and unchanged native acceptance. There are no pairs/cuts in these controls, so 85a's pair-only set equals the tested legacy set. This is explicitly not an execution of a historical S51 certificate.

`S51-FOCUSED-SPEC.json` targets exactly `inX: no quorum canVote/3 @step`, case 5. It records member-local `scoped.unused` deletion as well as family membership: widening the family alone cannot restore a deleted instance supplier. The named S51 decline identifies transport failure, **not the actual missing row or its supplier**. Its runtime certs/contexts were not exported. No guessed certificate or public-model reconstruction may be called the old replay.

See `R1.md` for historical cancellation correction, `GENERALIZED-SUPPLIERS.md` for the new boundary, and `INPUT-STATUS.json` for missing historical payloads.
