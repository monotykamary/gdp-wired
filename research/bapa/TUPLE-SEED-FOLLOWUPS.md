# Untrusted tuple seed follow-ups

These adapters produce **candidates**, never assumptions, source transports, or certificates.
No file under `kernel/` is changed. The public machine and public law array stay unchanged.

## Already-native tuple source keys

The `client_server_db_ae` retained family uses native `tup` keys. Its previous 0/27
preflight treated every non-arithmetic key as an unsupported packed expression.
The restater now recognizes the canonical right-associated tuple shape, preserves
coordinate order, and applies the same explicit layout, arity, bound-variable and
sort-conflict checks as the legacy packed-key path. It adds no domain bounds.
Left-associated tuples, wrong arities, undeclared maps, and unclassified expression
coordinates still fail closed. In particular, this is **not** a ghost-map alias or
an existential G-point injection.

## Tuple SUMs are not unary native SUMs

`MapRef(Message, 0).sum()` declares a unary read. When `Message` is actually read
or written at an arity-two key, materializing that declaration makes the unchanged
kernel's arity check reject it. The previous fixture did not expose the bug because
it declared `Message` but never used a tuple key.

The seed adapter now registers native whole-cell SUMs **only for unary maps**.
For a supported positive linear bound involving one tuple SUM, it instead proposes
one law containing two finite sub-sum bounds, over complete coordinate vectors
`p` and `q`:

```
H + M[p] <= B
p != q  =>  H + M[p] + M[q] <= B
```

Here `p != q` is a disjunction of coordinate inequalities, not a requirement that
all coordinates differ. Every coordinate is universally quantified; no radix or
finite-size bound is added. Positive coefficients and all other positive LHS terms
are preserved. Unsupported signs, nested arithmetic, RHS occurrences, and multiple
tuple totals fail closed.

The declaration audit reports `status: tuple-proposal`, `projection: finite-subsum`,
and `globalTotal: false`. The law audit records `tupleSumProjection`. Only a genuine
unary SUM name is given to `withSumsOf`; no `sum$Message` variable is materialized.

This is **not an exact global tuple total**. At budget two, three distinct unit
cells satisfy all two-cell bounds while their total is three. Even when unit-budget
exclusion suffices for a public protocol, its premises and resulting helper family
must be proved anew by the native checker. Retained proof success conveys no trust.

## Validation

The public-path regression now actually writes a binary `Message` key. It requires:

- arity two before and after the genuine unary SUM lowering;
- a complete native kernel-checked family containing the projected helper;
- the original public machine and laws in the capture, with no added public SUMs;
- rejection of a false helper and refusal to prove a false goal after changing the
  binary write from removal to insertion.

Additional tests cover canonical binary/ternary source tuple ordering, invalid
layouts, wrong association/arity, unclassified coordinates, and sort conflicts.
Pinned-Bun batch `20261115-221754-4y18os` passed all 3 native-tuple tests (14
assertions). The exact database audit improved from 0/27 to **23/27 candidates**,
with zero public proof calls and unchanged supplied source. The remaining source
indices 0, 1, 2, and 26 reference private witness maps `ResponseSent$w`,
`DbResponseSent$g`, or `DbRequestSent$g`; they remain explicit refusals, not aliases.
The full audit is in
`runs/native-tuple-seed-01/native-tuple-source-preflight.files/client_server_db_ae.json`.

Pinned-Bun batch `20261115-222912-s1q65p` passed typecheck, **36 tests / 206
assertions**, and commitlint. The test used committed baseline core snapshots
(separate from the capture and existential changes). Both actual binary-write
public-path controls passed, and the complete projected family rechecked.
Artifacts: `runs/seed-followup-03/seed-followup-tests.files/`.

No protocol proof or new all-size result is claimed by this document.
