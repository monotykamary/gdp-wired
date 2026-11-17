# Agent consultation MCP — prototype design

Branch: `feat/agent-consult-mcp`. Local stdio only; no HTTP listener, telemetry,
network fetching, package installation or model calls. **Research prototype,
not promoted until the surface-semantics release gate passes.**

## Contract

Five tools return stable compact JSON plus one deterministic paragraph using the
rule's own names. This is a transport/validation/explanation adapter over current
GDP-Wired APIs, never a new prover, search algorithm or equivalence engine.

- `prove`: supplied rule artifact and laws → existing proof verdicts. Say
  `proven` **only** when `proven && checked`; preserve unknown/refusal otherwise.
- `why_not`: return an existing checked counterexample, in declared state/input
  names. Do not invent a trace or call it minimal unless existing machinery
  establishes minimality; state the actual minimization guarantee explicitly.
- `suggest`: existing `inferLaws` / `discover` outputs, pasteable law source and
  existing refuted near-miss candidates with their counterexample. No LLM text.
- `check_change`: two bound revisions → laws still checked, newly broken with
  checked traces, and existing compose/refinement verdicts. Missing correspondence
  or unsupported refinement is a typed refusal, not inferred equivalence.
- `status`: preserve evidence-bound `proven`, `conformance`, `harness-checked`,
  `not adequate` and refusal results. No promotion from a supplied label alone.

Inputs are bounded, schema-validated data or explicitly registered trusted local
rule artifacts. Never eval client-supplied source, shell commands or remote URLs.
The prototype supports two checked-in example rules; unsupported constructs get a
named refusal and exact actionable fix rather than a silent approximation.

## Determinism and soundness

A request declares bounded counters (API calls/candidates/steps as supported by
existing APIs), consumed in stable order. No wall-clock policy or timeout is an
answer. Before selecting each existing API, verify its counted-budget capability;
if the API only offers elapsed-time search, do not expose it as deterministic.
Return a typed `counted-budget-unavailable` refusal with the exact missing API
support rather than adding a search engine. Report consumed counts and limits.

All requests/results bind rule/revision/law identities. Proof-check failures,
unsupported observations, absent native evidence and exceeded budgets have stable
codes and fixes. JSON serialization must handle bigint/nonfinite values explicitly
and never replace missing proof checks with truthy fields. Stdout is JSON-RPC only;
diagnostics go to stderr. MCP initialization, tool schemas and errors remain stable.

## Validation and delivery

1. Inspect current proof/search/discovery/refinement/status APIs and record actual
   supported seams before implementation; capability gaps remain explicit.
2. Implement a minimal stdio MCP adapter and update the repository GDP-Wired skill
   with when to call each tool and how to interpret refusals/unknown outcomes.
3. Unit-test success, broken law, unchecked proof, counted exhaustion, malformed
   input, unsupported construct, status tampering and deterministic replay.
4. Exercise all five tools in one scripted agent-style session on two example
   rules; retain compact transcript, hashes and counted receipts. No promotion
   or universal/native equivalence claim from this demonstration.

## Implemented scope (prototype)

The implemented entry point accepts only the allowlisted scalar Machine/Law JSON,
not registered files or source strings. `status` currently preserves only checked
rule-model proofs from this server's own workers; it refuses missing native
evidence instead of manufacturing `conformance` or `harness-checked`. Connecting
the existing native evidence validators remains a separate, owner-reviewed seam.
Hard counters are the existing full-profile work ledger and top-level API calls.
Inference's candidate/sample settings are soft hints, not extra exact budgets.
Existing finite search supplies the bounded shortest trace; absence is unknown.
Existing overflow checks remain authoritative. Internally generated validated AST
may be JIT compiled by the existing engine; this is not a no-eval/CSP sandbox.
See `README.md` for limits and `RESULTS.md` for actual development evidence.

Use genuinely tiny local checks where possible. Nontrivial builds/tests use the
ordinary interactive boat development lane, with cached tools/dependencies and
small outputs; strict-once is only for later acceptance evidence. Preserve parity
work separately; no reader deletion or label changes in this branch.
