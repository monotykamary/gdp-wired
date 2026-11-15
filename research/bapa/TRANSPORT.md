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

No family has been lifted by this file. In particular, generic matrix transport
is not the requested certificate transport, and `cutoff <= 64` is not evidence
that a fixed-64 certificate covers a smaller relational model.
