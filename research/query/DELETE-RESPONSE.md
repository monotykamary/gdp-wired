# Pure offline deletion-response validation

`delete_response.py` is separate research code. It imports only standard-library pure parsing/data helpers; it performs no network, credential, environment, filesystem, subprocess, provider or clock I/O. It is not wired into the accepted controller or any sender.

## Inputs and outputs

- `decode_acceptance(status, body, context)` accepts exactly HTTP 202 and returns a validated operation ID. It never marks acceptance terminal, even if that response embeds a completed operation.
- `decode_operation_response(status, body, context, expected_operation_id)` accepts exactly HTTP 200 and correlates the exact operation, target, kind and reason. A completed operation with consistent timestamps and optional stage yields `terminal=True`; other documented statuses remain nonterminal.
- `body` must be immutable complete message bytes. `RequestContext` carries the expected target/kind/reason and two caller assertions: `authenticated_account_bound` and `response_complete`, both defaulting false. These assertions must already be established by the transport. The parser cannot prove either. It does not demand TCP peer close: correct complete HTTP framing/stream completion suffices.
- `DeletionResponse` explicitly labels account binding conditional, authentication/framing unproved, native evidence false, and referenced data as possibly retained. It never claims global erasure. `terminal=True` is a conditional contract interpretation, not an observed provider action or a proof of physical erasure.

No account field is invented or trusted in the response. Unknown extension fields are validated as bounded JSON then discarded, not echoed or promoted to authority. Only the documented `deletion.operation`, `sandbox.deleting` and `snapshot.deleting` discriminator literals are accepted; the shared schema permits these and does not prescribe an invented per-phase literal.

## Strictness and local resource policy

Body limit: 65,536 bytes; nesting limit: 16; parsed-node limit: 4,096; numeric-token limit: 128 characters. These are local fail-closed resource policies, not claims about vendor limits. Strict UTF-8, complete JSON with optional trailing JSON whitespace, duplicate-key rejection (including escaped/nested keys), finite numbers, Unicode scalar values, exact required field types and documented enums are checked. Booleans/floats are not integer attempt counts. Background operation attemptCount is not a client-send count.

The bounded timestamp profile requires a valid calendar date, `T`, numeric offset or `Z`, and at most six fractional digits; leap seconds and broader representations are conservatively refused. Completed timestamps cannot precede requested timestamps. Nonterminal responses cannot carry completedAt or a completed stage. For completed status, completedAt is non-null and stage, if supplied, must be completed. Optional stage and expectedBy are otherwise genuinely optional; no account property or undocumented dependency is added.

Errors contain fixed codes only. Parsing errors are rethrown outside handlers so their diagnostic exception chain does not retain a raw-body JSON/Unicode exception. This is a diagnostic non-echo policy, not a memory-secrecy claim about a caller inspecting Python frame locals. Returned fields are normalized known operation fields; unknown possible secrets are not retained.

## Contract and boundaries

Pinned OpenAPI SHA256: `9f2abcf0735ba6230fba1b40ac9a11fe9022348997152821f3b99a1f7c2421fc`.

- https://docs.boat.dev/api/reference/sandboxes/permanently-delete-sandbox-data.md
- https://docs.boat.dev/api/reference/account/get-deletion-operation.md
- https://docs.boat.dev/data-retention/delete.md

A delete's acceptance is not completion. The documented completed state is scoped to the target; data independently referenced by a fork, newer snapshot or saved snapshot can remain. This module never treats a 404 or list disappearance as positive proof.

Creation stays blocked. The public template guide explicitly says an existing share code deploys the new save when the same name is saved again (`runs/sol-transport-research-v2/templates.md:298–303`). Neither names nor share codes are immutable artifact selectors; no code was generated or used.

Tests in `test_delete_response.py` use synthetic contract fixtures only. They make no provider, filesystem or credential calls. They do not run or modify the accepted controller, historical state-law proofs, or saved proof packets. The one ordinary scheduler test job is not native allocation evidence. No universal parser proof, native/R3/full-gate claim or live binding follows.
