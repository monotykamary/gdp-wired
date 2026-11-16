# No-search transport: `toy_consensus_forall`

## Identity and specialization

Retained 0.49 capsule:
`33f1a9949fb71fec0b5c1017c0607b25517a4222de10f0634bddc9bd4d8ae84b`.
Eight counted-family laws, sixteen init/step obligations.

Unlike `sharded_kv`, this emitted certificate has **no radix-64 packed keys**:
its maps and counts use unary keys. Key translation is therefore the identity
for this first target. This does not implement the still-needed general
packed-key-to-tuple translator.

`CertificateBoundErasure.lean` is a generic candidate transformer. It erases
literal `< bound` / `<= bound` conditions from the machine, laws, annotations,
and conditional expressions. It keeps count coefficients and surviving
arithmetic leaf proofs, and prunes splits for erased bound comparisons.
This operation is not universally sound by itself: **the complete translated
family must pass the existing checker**. `checked_counted_transport` states
this conditional soundness contract.

## Pruning and its soundness guard

The annotation-only rewrite checked fourteen obligations. The two failing
steps were public law 2 and auxiliary law 4. They split on `z<64` and closed
the complement using a `z<=63` row from the old negated goal:

- Law 2: paths `YYN` / `YN`, `fact21`, columns 7 / 13, constant -63.
- Law 4: paths `YYN` / `YN`, `fact19`, columns 16 / 10, constant -63.

Those rows are invalid after guard removal. The transformer keeps the former
`<64` subtree and checks it for **all target values**, not just values below
64. The complete checker starts the resulting tree at an empty path. It
inherits neither the removed split nor a bounded-sort assumption.

`ToyConsensusForallControls.lean` checks absence of surviving 64-bound leaf
rows. Its deliberate negative copy appends `z<=63` with the old `fact21` hint
to a surviving safety leaf, keeping all existing input indices and proof
steps. Both its step and family checks must reject it. The unpruned tree is
another negative control: deleting annotations alone was insufficient.

## Positive result and scope

Batch `20261115-223306-8ogmxw` checked all sixteen obligations and the full
family, native exit 0. `no_size_cap` and `check` use only `propext`; `laws`
uses only `propext`, `Classical.choice`, and `Quot.sound`. The retained proof
was rechecked first. No search, new count instance, supporting law, or
protocol execution was used.

This is a direct lift for the transformed **numeric machine**, with no size
cap and with value bounds removed from laws and request admission. It is not
a source/TLA+ correspondence or projection theorem. The stronger surviving-row
negative control and unchanged-semantics checks **passed** in batch
`20261115-223708-fr8lvz`, native exit 0. All sixteen checks are true;
no surviving bound rows remain; both the mutant step and mutant family are
refused. Count definitions, request evaluation, and transition evaluation
are unchanged. All printed axioms remain within the three allowed axioms.
The retained source SHA-256 is
`27b6b6c2295c7e444999c16e84abd7e56e871f2d4100b39980af416a5cd7b1bf`.
Per-obligation rows are retained in `toy-transport.tsv`.

## Reproduction

Use `toy-transport.jobs.json` only through supercomputer, with
`SUPERCOMPUTER_CONTROLLER=1 SUPERCOMPUTER_NO_BUILD=1`. Supply the exact retained
`normal28-family-toy_consensus_forall.files/lean` directory as
`--data ...:transport-retained`. The job rechecks the old proof, compiles the
translator, checks the new family and controls, prints axioms, and runs
commitlint. It makes no public prover call.
