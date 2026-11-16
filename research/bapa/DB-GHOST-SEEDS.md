# Native tuple ghost seed proposals

`seed-audit-client_server_db_ae.json` opts into `ghostBindings` and selects the
original public existential. These bindings describe proposed private maps,
not aliases for relation rows:

| Retained map | Key sorts | Value sort |
|---|---|---|
| `ResponseSent$w` | Node, Response | Request |
| `DbResponseSent$g` | DbRequestId, Response | Request |
| `DbRequestSent$g` | DbRequestId, Request | Node |

`native-ghost-seeds.ts` copies the retained zero-start point updates to fresh
private map names. It keeps complete native tuple keys and binds the public
witness by relation-coordinate roles, not generated binder names or order.
Flags refer to the sized port's actual flag definitions. Unknown flags, missing
ghost declarations, inconsistent roles/layouts, nonzero starts, unsupported
updates, and ambiguous witness bindings are refused.

Helper reads of a ghost cell become a fresh universal value under equality to
that exact cell. Multi-coordinate keys remain complete; repeated identical
reads share one value. Thus nested ghost reads used as native tuple coordinates
can be restated without assuming that a relation row exists. Every helper is
still an untrusted candidate.

The public entry uses the existing checked existential route: `ghostedOk`,
`someOfGhostsOk`, the complete native family proof, and `checkGhostedLaws`.
Neither the original public law nor source machine is mutated. No kernel file
is changed.

## Validation

Pinned-Bun batch `20261115-232713-5od19y` passed typecheck, **42 tests / 235
assertions**, and commitlint. This includes a genuine public `proveRule` test
with a binary-key ghost witness and a complete native family recheck, plus
wrong-layout, missing-ghost, nonzero-start and unknown-flag negative controls.

The actual sealed DB capsule now yields **27/27 candidates, zero drops**, one
witness proposal, and three fresh ghost maps. Its proposed producer passes
`ghostedOk`. The no-search audit made **zero public proof calls**, incurred no
native search work, and left the supplied source object unchanged. This is not
a checked proof of the actual DB protocol; p3 must make its seeded public call.
The separately disclosed rematerialization flag is not source qualification.

Receipt: `DB-GHOST-SEEDS-RESULTS.json`. Full gate artifacts:
`runs/db-native-ghost-02/db-native-ghost-gate.files/`.

Use `--seed-candidates research/bapa/seed-audit-client_server_db_ae.json` with the
existing `seed-capture-client_server_db_ae` capture mount. This patch builds on
the checked existential candidate route in `eda64a393`.

No DB protocol rerun, source-qualified Lean result, or new all-size claim is
made by this adapter or preflight.
