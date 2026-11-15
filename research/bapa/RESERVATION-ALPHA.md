# Reservation witness alpha-renaming

A count proposal owns a semantic count instance, not the spelling of the fresh
witness that happened to be generated for it. `reservePool` now freshens that
binder when its spelling collides with source reservations. The semantic key,
count definitions, bounds, read bindings, and original goal remain unchanged.

A prior lease whose witness is read freely by the rebuilt goal is different:
changing only its binder would sever a live dependency. It is still refused.
Unselected pick terms are renamed with their proposal binder. Selected pick
dependencies, captured read keys, declaration/bound capture, stale semantic
identities, and duplicate owners remain refusals. No kernel file is changed.

Successful alpha steps are retained in `reservePool(...).record.renamed`, emitted
as `countsDump` events with phase `reservation-alpha`, and recorded as untrusted
`proposalProvenance` on the generated count certificate. They are not premises;
the ordinary native family check remains the authority.

## Regression and evidence

Pinned-Bun batch `20261115-231624-emjq9p` passed typecheck, **54 tests / 972
assertions**, and commitlint. Both public tests reach checked seeded admission
and recheck the complete counted family, including retained rename provenance.
One uses the unmodified public path; the other isolates the untrusted pass-one
proposer. Both retain the real public API, proof builder, and native checker.
Their explicit initialization guard leaves the real sum bound required after
every step. No fallback verdict is accepted as seed admission evidence.

Unit controls retain refusals for a selected dependent pick and for a previously
leased witness read by a new PRE hypothesis. Original source/pool inputs are
unchanged. Receipt: `RESERVATION-ALPHA-RESULTS.json`; full artifacts:
`runs/reservation-alpha-06/reservation-alpha-gate.files/`.

A read-only audit of retained output found ten occurrences of the exact refusal
in p2's 1056-event instrumented toy-consensus run: the public goal and retained
seeds 2 and 4. The inspected sharded, no-lost-keys, and p1 worker logs contain no
matching text, but those logs do not instrument swallowed proposal exceptions.
Their absence is **not** evidence that those calls avoided the same collision.
No protocol search was rerun for this audit.
