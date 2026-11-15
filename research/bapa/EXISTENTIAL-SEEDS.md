# Checked existential candidate proposals

The ordinary candidate route may receive `candidateSeeds.witnesses` (by public
law name) and `candidateSeeds.ghosts` (fresh scalar/map definitions). They are
untrusted proposals, not caller facts or assumptions. The public laws and source
machine are not rewritten in place.

For each public existential, the route requires one term for every `Law.some`
binder. It substitutes those terms, prunes candidate helpers, and checks the
complete resulting family. It also requires the existing kernel checks
`ghostedOk`, `checkGhostedLaws`, and `someOfGhostsOk`. The retained provenance uses
the existing `skolem` context and includes the full checked producer family.

Public goals may not read new ghost state. Helpers may. Unknown or incomplete
witness bindings, colliding ghost names, unsupported public metadata, and failed
whole-family checks are refusals. A failed seed attempt adds no assumptions to
ordinary fallback. No file under `kernel/` is changed.

## Retained no-lost-keys witness

The explicit `existentials` selection in
`seed-audit-sharded_kv_no_lost_keys.json` opts into a restricted source adapter.
It matches binders by actual `Owner` and `TransferMsg` coordinate roles, not by
arbitrary generated variable names or their position in `Law.some`.

The captured witness is:

```
owner = Owner$n[k]
message = 4096 * TransferMsg$n21[k] + 64 * k + TransferMsg$v1[k]
```

The sized native law has four existential coordinates. The proposal supplies:

```
owner = G_owner[k]
node  = G_transfer_node[k]
key   = k
value = G_transfer_value[k]
```

The three fresh ghost maps start at zero. Their proposed point updates come from
the retained producer, with map names restated and packed tuple comparisons
converted to native tuple comparisons. The adapter does not claim the old
producer is a proof of the new machine.

Retained helper reads `G[k]` are abstracted to a fresh universal value `u` under
`G[k] = u => ...`. Repeated identical reads share a value. This equality-guarded
transformation does not assert relation membership or omit absent-row cases.
The ordinary candidate restater then maps explicit bounds to sized domains.
Every resulting helper and the original native public goal must still check.

## Validation status

Pinned-Bun batch `20261115-223654-l2u6tl` passed typecheck, **41 tests / 230
assertions**, and commitlint. The genuine public `proveRule` fixture admits the
seed route, retains its supporting helper and complete producer family, and
rechecks its ghost projection. Missing/tampered witnesses, false helpers, and
public reads of new ghost state are rejected.

The actual sealed no-lost-keys capsule yields **10/10 candidates, zero drops**,
one two-to-four-coordinate witness proposal, and three ghost maps. The adapter
uses the complete retained leaf, not only the Skolem context's initial family.
This audit made **zero public proof calls** and left the supplied source object
unchanged. Its rematerialization flag remains separately disclosed in the
receipt; it is not a source-equivalence or Lean qualification claim.

Receipt: `EXISTENTIAL-SEEDS-RESULTS.json`. Full artifacts:
`runs/existential-seed-02/existential-seed-gate.files/`.

No protocol rerun, source-qualified Lean result, or new all-size claim is made
here. The normal worker can now use this manifest for a single seeded public
call; `candidate-proposals.json` retains the exact untrusted laws, terms, and
ghost definitions even if admission is inconclusive.
