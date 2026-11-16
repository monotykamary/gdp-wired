# Source inference wrappers around retained witnesses

Extends the shared multi-parent witness bridge (`e96db114a`), not the native
prover or trusted Lean kernel. No search is used.

A retained candidate-seeding proof has a source-side inference wrapper above its
Skolem context. Its source machine differs from the ghost-extended producer,
and its public existential statement differs from the producer's substituted
plain statement. These differences must not be papered over by skipping contexts.

`proof-witness.ts` now records each inference context's provenance path:

- **Above that path's witness:** the wrapper's original machine must be deeply
  identical to the capsule source, with equal SHA-256 of its JSON representation.
  Every original public law must occur unchanged, exactly once; duplicate names
  are refused. Additional inference claims must occur unchanged, exactly once,
  in that path's complete producer family.
- **Below the witness, or on a context-free sibling path:** preserve the existing
  producer-machine and complete-family membership checks.

Every path still goes through the existing source/witness substitution checks,
native `checkLaws` on the complete family, and retained Lean emission. No wrapper
or candidate law is appended to machine facts or supplied as an assumption.
Retained seeds are derived laws with their own start/step certificates. A missing
seed certificate is a refusal, not a license to trust that seed.

## Controls

`source-inference-witness.jobs.json` runs scoped TypeScript, all existing witness
and source-projection tests, the new source-wrapper controls, and a complete Lean
build/root/axiom gate for a synthetic existential with an additional proved seed.
The fixture is constructed from constant contradictions, not a prover call.

Negative controls refuse: a changed source transition; a missing, changed or
duplicated public law; an extra claim absent from the complete family; and removal
of a retained seed's step certificate. Existing multi-parent controls remain.

Validation: strict-once batch `20261115-234253-o3pjqq`, native exit 0 (36.27 s).
Scoped TypeScript passed; 22 tests / 51 assertions passed, including every listed
negative control. The 27-target Lean build, explicit root check, axiom gate and
commitlint passed. The source existential and complete family theorems depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

Artifacts: `runs/bapa-p4-source-inference-controls/source-inference-controls.files/`.
The real no-lost-keys capsule is not rerun by this control recipe; its one
authorized no-search source retry follows the shared fix.
