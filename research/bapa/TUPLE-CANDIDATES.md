# Native tuple row candidates

The quorum and loaded-field candidate generators now recognize homogeneous
native tuple rows as well as the existing numeric packed rows. This repairs a
candidate-vocabulary gap; it does not prove MLDR or authorize replacing its
symbolic relation with a finite packing base.

## Representation

- A row read may be `Config(tuple(row, member))`, with matching relation sorts.
- A tuple row update uses the first and second projections of its `each` key.
- Derived two-row counts use **one plain natural pair key** and project its
  components in the definition. They do not read a count map at a tuple
  expression, which the current checker disallows.
- Reversed row definitions have distinct count maps. Only the exact projected
  tuple orientation is collapsed back to a plain count key; unsupported
  orientations cause that candidate to be omitted.
- Packed keys keep their existing path. No fixed or guessed size is introduced.

The field generator recognizes tuple row loading and marker-restricted row
agreement. All outputs are untrusted candidates for the unchanged checker.
The legacy stored-guard provenance format describes a numeric width; native
tuple candidates deliberately do not forge that metadata. Its special lifted
proof route is not extended here; ordinary candidate checking remains available.

## Verification and scope

The fixture suite compares every generated packed quorum law with its native
tuple counterpart after explicit pair substitution and projection reduction.
It covers asymmetric row directions, loaded-row/marker field proposals,
unrelated rows, Boolean row lowering, scope/map arities and counted-obligation
construction. Batch `20261115-205501-ms78yb` passed types, commitlint and
36 tests / 213 assertions, with one pre-existing exact-lease test skipped.
The preceding independently reviewed parity run was `20261115-204829-dqhbtd`.
No skipped test is counted as verified.

Source inspection found that quorum leader election has no stored-row pattern;
majorityset's row-majority input lacks this generator's carried-set/stored-row
assumption shape; and the sharded-KV variants have heterogeneous tuple state
without the relevant majority/copy-marker pattern. They are not silently
classified as fixed by this change.

No MLDR or protocol search was rerun. MLDR remains UNKNOWN until its lane runs
the repaired generator and retains a complete checked family, followed by the
normal split, source-projection and axiom gates.
