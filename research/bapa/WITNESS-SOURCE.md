# Retained witness source export

`proof-emit.ts --projection witness` reads the existing hash-bound capsule in a
fresh process. It restores the retained term prelude, checks the complete usual
producer family, and emits a source existential theorem. It does not search for
new helpers, witnesses, or proofs. The ordinary/quantified/row-alpha and counted
routes remain separate.

The supported provenance has checked `witness` or `skolem` contexts and complete
usual producer families. Single-path behavior is unchanged. For multiple parent
paths, every path gets its own checked family and source witness theorem; the
public result conjoins all of them. A context-free inference path may reuse the
unique retained witness context only after its complete machine, law membership
and source substitution pass the same checks. Ambiguous context reuse is refused.
See `MULTI-PARENT-WITNESS.md` for the coverage contract and negative controls. The
exporter uses `bundle.original.laws`, not the context's possibly augmented law
list, as its public contract. It checks original-machine equality, public body
and binder identity, exact captured substitutions, full-family membership and
the native certificate. Captured witness-selection advice may be ignored, but
advice in the original public contract and unsupported public metadata are
refused. Auxiliary ghost-map laws stay in the full checked family.

## Bound and map witnesses

A retained scalar witness may have the same name as its source existential
binder. `BoundGhost.lean` proves that updating both valuations with the same
existential assignment makes them agree also at the bound ghost names. The
transfer therefore requires avoidance of only the *unbound* ghost variables;
it still requires avoidance of **all ghost maps**. No original body or binder
is renamed in the emitted source theorem. `GhostMap.lean` is unchanged.

For captured map witnesses, the exporter reconstructs ghost starts and writes
from the retained machine and checks that its whole machine is exactly the
corresponding ghost extension. The source substitution reads only the captured
map at the captured key. It does not invent a witness value or omit a helper
obligation.

The generic theorem and positive/negative controls passed pinned-Bun,
Lean-4.34.0 batch `20261115-211748-yf1kig`. Its axiom output is the allowed
`propext`, `Classical.choice`, `Quot.sound`, not an axiom-free claim.

## Source evidence

`20261115-212112-lbbodo` passed 12 tests / 31 assertions, types and commitlint,
and complete Lean/source/axiom checks for:

| Protocol | Original existential theorem | Receipt |
|---|---|---|
| `simple` | `bapa_simple_ex0` | `runs/bapa-witness-source-01/witness-simple.files/SOURCE-CHECKED.json` |
| `simple_regular` | `bapa_simple_regular_ex0` | `runs/bapa-witness-source-01/witness-simple_regular.files/SOURCE-CHECKED.json` |

That batch's `client_server_ae` case stopped at an overly restrictive equal-law-
count guard. Its ghost-map witness legitimately introduces an auxiliary law.
The corrected exporter selects the exact public plain by unique name and still
checks the complete family. `20261115-212533-rlk0w1` then exposed the legacy
one-key pretty-printer restriction. The explicit multi-key ghost-substitution
theorem now handles that case without dropping any family law.

`20261115-212838-embmgp` passed the isolated `client_server_ae` source, Lean and
axiom gates plus the 12-test unit gate. Its source theorem is
`bapa_client_server_ae_ex0`; the checked receipt is
`runs/bapa-witness-source-03/witness-client_server_ae.files/SOURCE-CHECKED.json`.
All three projects contain identical checked `BoundGhost.lean` and generated
library bytes. The two successful scalar-source builds were not rerun.

`witness-source-verify.ts` checks all emitted-file hashes, original input hash,
full-family theorem, exactly one source theorem for each original public law,
clean completed Lean log and allowed axiom output. Only that enclosing receipt
is labelled `SOURCE_CHECKED`; nested emission metadata stays
`EMITTED_NOT_CHECKED`. This is evidence about these encoded source laws, not a
blanket 29/29 claim or external source-language correspondence proof.
