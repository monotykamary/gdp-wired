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
- Candidate per-sort bound: constants + existential witnesses + one nonempty
  filler. It is not yet a proved cutoff in this commit.
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

## Outstanding gates

1. Actual obligation-to-fragment and fragment-to-retained-numeric-model bridges,
   with exact function/flag/update semantics and certificate coverage.
2. Small-satisfiability theorem for the declared fragment.
3. Checked recognizer for the actual 67 declarations / 897 inventory entries.
4. Per-family no-search lifts only after every required obligation passes.

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
proof, a relational-recognizer result, or a lift of the other 66 declarations.

The generic relational file itself has not lifted any family. In particular, generic matrix transport
is not the requested certificate transport, and `cutoff <= 64` is not evidence
that a fixed-64 certificate covers a smaller relational model.
