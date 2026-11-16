# Countermodel transport — proof lane

## Checked foundation

`RelationalFragment.lean` defines a finite many-sorted relational signature,
well-sorted terms and quantifier-free matrices, with satisfaction meaning
`exists witnesses, forall universal assignments, matrix` — the intended
**negation of the complete verification obligation**, never the safety goal
alone. Constants and equality are supported. Relations have arbitrary finite
arity. There is no implicit interpreted order, cardinality or arithmetic.

- Empty-sort policy: every declared sort must be nonempty. Zero-size cases are
  explicitly outside this first fragment and cannot be inferred from its proofs.
- Function policy: no positive-arity function symbols; closure depth and added
  function witnesses are exactly zero. State represented by relations does not
  license interpreting an arbitrary total function as a relation without its
  totality/functionality proof.
- Per-sort bound: constants + existential witnesses + one nonempty filler,
  proved in `RelationalSmallModel.lean` (the initial syntax commit alone did
  not prove it).
- Domain policy: fixed-64 sorts are excluded from certificate lifting unless a
  separate padding theorem is supplied. A restriction embedding is not padding.

`Term.eval_embedding` and `Matrix.eval_embedding` prove satisfaction equivalence
for assignments along **induced injective** embeddings, including negation and
equality. They do not preserve universal truth when *adding* new elements and
do not themselves establish any connection to the exported numeric machines.

Verified through supercomputer/axiom-gate, batch `20261115-162142-cfugbh`:
all four printed declarations pass; axioms are respectively none, `propext`,
none, and `Quot.sound`. Prior batch `20261115-161407-giian1` failed on use of
the reserved identifier `Sort`; retained as failed, not counted as a success.

## Checked numeric representation

`RelationalNumeric.lean` proves tuple-code injectivity and represents every
finite relation as an existing-kernel `Nat -> Nat -> Nat` table. The compiler's
`Matrix.compile_correct` theorem preserves equality, relations and all Boolean
connectives; `Satisfies.numeric_iff` preserves the full existential/universal
assignment quantification. Native tuple keys (not literal radix64) are used.

Batch `20261115-164203-wpgkpx`, `relational-numeric`: PASS including all seven
printed axioms and conventional commit validation for `795dbc655` and
`bb7fa0a2a`. Only `propext`, `Classical.choice`, `Quot.sound` appear. This is an
encoding theorem, **not** an assertion that any old certificate checks its
compiled formula. See `TRANSPORT-OBSTACLE.md` for the missing exact obligation
bridge. The same batch's independent small-model job failed; it is not green.

## Checked small-satisfiability cutoff

`Bapa.Relational.small_satisfiability` constructs a model with each sort
of size at most constants + existential witnesses + 1. It handles aliasing by
first constructing a duplicate-free enumeration, not assuming the witnesses
are distinct. The induced model preserves equality and relations, hence all
Boolean connectives; the universal assignment is pushed into the original
model. `unsatisfiable_of_small` is the corresponding conditional logical lift.

Batch `20261115-164543-pa07sd`: the small-model module and all three printed
axiom reports passed. That overall job then failed in the separately compiled
padding control on numeral elaboration; no whole-job PASS is claimed. All
small-model declarations use only the three allowed axioms.

The augmented tcommit control batch `20261115-164428-yq4uwp` passed independently:
request and step semantics are unchanged, and both stale/mismatched cap
annotation variants are rejected. No proof tree or table was changed.

## Final verification and stopping point

- `20261115-165537-5hw7av`: **PASS**, all four generic Lean modules and all
  five conventional commit messages through the existing gates. The four
  exported `.lean` files byte-match the final worktree files. All printed
  theorem dependencies are within `propext`, `Classical.choice`, `Quot.sound`.
- `20261115-165421-74qocy`: independent commitlint-only **PASS** for the same
  five messages.
- `20261115-164428-yq4uwp`: **PASS**, rechecked retained tcommit source plus
  all ten direct-lift / operational-preservation / negative-control theorems.
- Failed iterations remain under `runs/bapa-transport/`: elaboration errors
  were not counted as proofs. The v5 attempt failed while shipping because
  this lane edited documentation before upload completed; it did not supply
  a Lean result. The stable-tree v7 gate above is the final result.

The fixed-size control proves a sentence with cutoff 2 is satisfiable at size
1 and unsatisfiable at size 64, so the fixed-64 exclusion is essential, not a
padding assumption hidden in the cutoff theorem.

**STOP at the exact retained-obligation bridge**, not at a blanket impossibility
claim. Full requested step 2 (matching the generic numeric instances to old
certificates) remains unproved; the abstract requested step 3 is now checked;
requested step 4 (67-declaration recognizer) has not been implemented. Do not
claim the generic cutoff lifts any family. Independent direct lifts now include
tcommit (unchanged proof tree) and toy_consensus_forall (checked pruning of
obsolete bound splits, with surviving-bound negative controls). See
`TOY-TRANSPORT.md` for the latter. Complete per-case outcomes
are in `TRANSPORT-RESULTS.md`; the exact mismatch is in `TRANSPORT-OBSTACLE.md`.

## Outstanding gates

1. Actual obligation-to-fragment and fragment-to-retained-numeric-model bridges,
   with exact function/flag/update semantics and certificate coverage.
2. Checked recognizer for the actual 67 declarations / 897 inventory entries.
3. Per-family cutoff-based lifts only after every required obligation passes.

## Concrete direct certificate lift: tcommit

`TCommitCertificateTransport.lean` supplies a separate **direct**, not cutoff,
proof-theoretic lift. It rechecks the retained original source and replaces only
`size <= 64` by `trueC` in the machine precondition and the named certificate
hypotheses. The variable tables and both proof trees are definitionally
unchanged (`tree_unchanged`, `table_unchanged`). The unchanged trusted checker
accepts the transformed certificate. There is no search or inferred invariant.

Batch `20261115-163558-lnd502`: original retained source recheck and all six
transport declarations PASS through the axiom gate. Retained `Proofs.lean`
SHA256 `f91cffaae3b8f737fd62110f604e7616cc791e0bac477f835d88666d4cf5a2d2`,
from the tcommit inventory receipt, capsule
`b852b4a00c3843be6eff351435a4414423af85d6162f59ece8f6a641c6cc37dc`.
The job mounts the retained `lean/` directory as `transport-retained`, rechecks
`Proofs.lean`, then imports that rechecked module for the transport.

`safety` states the same numeric commit/abort exclusion for **every natural RM
size, including zero**, for the otherwise unchanged tcommit machine. The
unbounded RM sort is unary-keyed; no fixed-64 sort or radix change is hidden.
Axioms: tree/table/pre equality none; checker `propext`; laws/safety only
`propext`, `Classical.choice`, `Quot.sound`. This is not a TLA+ correspondence
proof, a relational-recognizer result, or a lift of the other 65 declarations.

The generic relational file itself has not lifted any family. In particular, generic matrix transport
is not the requested certificate transport, and `cutoff <= 64` is not evidence
that a fixed-64 certificate covers a smaller relational model.
