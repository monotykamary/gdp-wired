# Checked alpha transport for retained witness sources

Source-side inference still requires an identical source machine, or bound-name
alpha conversion checked in Lean. `witness-alpha.ts` applies proposed local
quantified-flag/row substitutions and compares the entire machine. Any non-alpha
change is refused. This syntactic preflight does not establish equivalence.

The emitted Lean checks `QAlpha.validAll`, `RowAlpha.validAll`, and exact equality
of the fully renamed source to the retained witness context's original machine.
Existing `QAlpha.renameAll_equiv` and `RowAlpha.renameAll_equiv` then derive
source reachability. The independently checked witness projection supplies the
original public existential or ordinary statement at that state.

No new Lean axioms, checker changes, search, source-law weakening or assumed
seeds. Complete-family and multi-parent checks remain. Public law bodies and
binders must be unchanged. Producer family proofs retain their original terms.

`sourceProjection.alphaTransports` records source/producer SHA-256, exact flag
and row renames, and all four checked theorem names. The receipt verifier requires
explicit axiom output for those names alongside public/family coverage. All
emitted files, including machine definitions and renames, are hash-bound.

`witness-alpha.jobs.json` builds an existential control with a proved seed, a
quantified-flag rename and a row rename. A non-alpha state update is refused even
alongside valid binder renames. Removing the quantified rename from emitted Lean
must fail its exact machine equality check.

Validation: batch `20261115-235605-y3mujn`, native exit 0 / 39.53 s.
Scoped TypeScript and 24 tests / 60 assertions passed. Full 27-target Lean build,
explicit root check, axiom gate and commitlint passed. The source existential,
family and reachability theorems use only propext/Classical.choice/Quot.sound.
The missing-renaming mutant failed exactly at `alpha_result`'s machine equality.

Evidence: `runs/bapa-p4-witness-alpha-controls-v2/witness-alpha-controls.files/`.
The first control gate (`20261115-235238-gqpvjx`) failed before emission because
my synthetic flag compared its bound key with itself, outside the kernel's
allowed key-only comparison shape. Replacing that test condition with `0 <= key`
fixed the fixture; no kernel/checker or transport contract was relaxed.
