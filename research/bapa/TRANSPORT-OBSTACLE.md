# Remaining certificate bridge gate

The generic relational development must not be mistaken for a transport to
the 67 *retained* declarations. Its numerical compiler uses one 0/1 map per
relation. The retained machines instead include multi-valued natural maps,
fixed-radix tuple reads, quantified flags, arithmetic and counted side conditions.
These are different numeric formulas until a checked elaborator relates them.

A concrete example is tcommit's single map `St`. Treating `St[x] = 1` and
`St[x] = 2` as independent unary relations admits a relational interpretation
where both hold at x. No numeric interpretation of the old single `St` map can
realize that model. A proper relationalization must include and prove sufficient
colour-disjointness / exhaustiveness constraints and the guard/update bridge;
a map-per-predicate representation theorem alone is insufficient. This is a
precise obstruction to applying `Matrix.compile_correct` directly to that old
certificate, not an impossibility result for a better encoding.

Likewise, `Satisfies.numeric_iff` (when checked) relates the declared typed
matrix to its own compiled numeric family. It does **not** identify that family
with `sStartGoal` / `sStepGoal` of any retained declaration, or prove that old
certificates cover those numeric instances. The inventory is receipt metadata,
not a first-order AST; it cannot supply that missing proof.

The chosen fragment explicitly excludes empty sorts and fixed-64 sorts. The
singleton countermodel control demonstrates why nonempty padding to 64 is not
available generically, even with a candidate cutoff below 64. Positive-arity
functions, order, cardinality and arithmetic are also excluded unless separately
elaborated with a checked semantic bridge.

Accordingly no checked recognizer for all 67 declarations has landed, no generic
per-family cutoffs are claimed, and the 28 families other than tcommit retain
their old scopes. The direct tcommit certificate transport is independent of
this missing relationalization: it keeps the old single-map representation,
request/step semantics, proof trees and variable tables, and the trusted checker
verifies the weakened parameter precondition without search.
