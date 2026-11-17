# Agent consultation: MCP and library

The supported adapter asks the **existing** gdp-wired engines whether a scalar-natural
model law has a checked proof, a reachable counterexample, or a missing inductive
invariant. It adds no inference/proof algorithm. This is a package integration, not
a new proof capability or a native/source-conformance certification. The counted
work profile is still provisional research machinery. Do not use `ok: true` alone
as a proof: require each relevant `proven === true && checked === true`.

## Start and configure

After installing a version of `gdp-wired` containing this surface (this change does
not publish one), run `gdp-wired-agent-consult`. Node >=20 is sufficient; no Bun,
MCP SDK, credentials, network service or model provider is needed for the data-only tools.
Opt-in workspace extraction additionally needs TypeScript beside the package and the
source language runtime (Python for `.py`), exactly as the CLI does. In a source checkout the equivalent is
`bun core/agent-consult/cli.ts`; build with the repository's normal build before
running `node dist/core/agent-consult/cli.js`.

Generic MCP client configuration (configure your client explicitly; nothing is
registered automatically):

```json
{
  "mcpServers": {
    "gdp-wired": {
      "command": "/absolute/path/to/node",
      "args": ["/absolute/path/to/node_modules/gdp-wired/dist/core/agent-consult/cli.js"]
    }
  }
}
```

Use an explicitly installed/pinned package; avoid an unpinned runtime download.
The CLI accepts **no arguments**, roots, modules, file paths or source code. It
reads newline-delimited JSON-RPC 2.0 MCP (protocol `2024-11-05`) on stdin; stdout is
protocol JSON only. `initialize`, `ping`, `tools/list`, `tools/call` are supported.
Results include both `structuredContent` and equivalent JSON text for older clients.
No HTTP transport, resources, prompts, dynamic roots or persistent database is provided.
The server name is now `gdp-wired-agent-consult` (formerly the research prototype's
`gdp-wired-agent-tools-prototype`). The original five tools and their v1 schemas
are preserved; the additional `check` tool has an explicit workspace trust boundary.

Workspace checking is a separate server-authorized opt-in: see
[workspace check trust/budget contract and native demo](agent-consult-workspace-check.md).
With no configured roots, `check` refuses and the original data-only default remains.

## Agent reasoning loop

1. Translate the rule and law faithfully to **data**, never a module to execute.
   [examples/agent-consult.json](../examples/agent-consult.json) is a complete
   `tools/call` request for a capped budget. Read `tools/list` for recursive schemas.
2. `prove {subject,laws,budget?}` returns per-law checked inductive verdicts.
   A failed induction step can be an unreachable state: it is not a real bug yet.
3. `why_not {subject,laws,budget?}` asks existing finite search for a reachable,
   interpreter-checked trace. Original parameter/input/state names are preserved.
   No trace **does not** establish a law. Trace minimality is length-first only
   inside the reported finite domain, not global minimality.
4. If no real trace explains the failed proof, use
   `suggest {subject,laws,nearMisses?,budget?}`. Existing `inferLaws` proposes helper
   invariants; only jointly checked support sets are returned as `discovered`.
   Keep `supportSource` with the goal; do not paste a helper while dropping the
   laws that support it. A missing invariant is not inferred from silence alone.
   `nearMisses` are caller-supplied candidates, not generated language-model laws;
   a returned near miss includes a real trace. `unresolvedNearMisses` are unknown.
5. `check_change {before,after,laws,budget?}` rechecks the same laws on revisions
   with identical unit, parameter, input and state names. `newlyBroken` requires
   an old checked proof plus a new reachable trace. `lostProof` is separate.
   Behaviour comparison is **directional refinement under the after rule's
   precondition**, using existing compose and both invariant/admissibility checks;
   it is not bidirectional/source equivalence.
6. `status {unit,revision}` uses the digest returned by a computational request.
   It never accepts labels supplied by a caller, substitutes another revision,
   or invents native evidence. Only `prove`/`check_change` populate its registry.
   `nativeLabel` is null. Unknown/evicted revisions return `missing-evidence`.

A `subject` is `{unit,rule}`. Rule data includes `name`, `params`, `inputs`,
initial `state`, `step.state`, optional `pre` and `assume`; laws are `{name,holds}`.
Terms: `var`, `const`, `add`, **truncated natural `sub`**, `min`, `max`, constant
`mul`, `if`. Conditions: `<`, `<=`, `=`, `and`, `or`, `not`. Signed values, maps,
functions, quantification, callbacks, source, modules, paths and URLs are refused by
the five data-only tools, not approximated. `check` alone accepts a local file path. Outputs include `assumptions`: exact initial/pre/request data
and laws bound into the revision. Retain those alongside proofs and suggestions.
A model proof does not assert the shipping program matches that model.

## Library

```ts
import {createConsultation} from 'gdp-wired/agent-consult'
const session = createConsultation()
try {
  const receipt = await session.call('prove', {subject, laws, budget: {work: 500000}})
  // Inspect receipt; only checked proof pairs establish model laws.
  const explained = await session.call('why_not', {subject, laws})
} finally {
  await session.close()
}
```

`call(tool,args,{signal?})` returns the structured data envelope.
`handle(jsonRpcRequest,{signal?})` returns a JSON-RPC response (or null for a
notification). Both serialize work per session. No engine is imported into the
host: each computational request uses a fresh installed worker with a fixed path
and sanitized environment. Status is session-local, bounded to256 revisions
(oldest entries evicted); a new session has no evidence. Importing the subpath
starts no server, worker, signal handler or stdin listener.

`AbortSignal` cancels library requests; `close()` cancels the active worker and
refuses queued tool calls; await its returned promise to join the exact child exit. On stdio, SIGINT/SIGTERM or closed stdin shuts down the
server and its own worker. MCP cancellation notifications are currently ignored;
use process termination to cancel stdio work. Worker exit is awaited before another
request starts. Cancelled work is refused and cannot populate status. There is no
reasoning wall-clock deadline; cancellation is not a proof or counterexample.

## Counted limits and refusals

Defaults: `work:500000`, `apiCalls:24`, `depth:3`, `bound:2`, `candidates:64`.
Caps: work5,000,000; API calls64; depth4; bound3; candidates256. Zero work/API
allowance is meaningful. `candidates` is an inference-pool **hint**, as is the
engine's128 samples, not a hard bound on all processing. Hard reasoning limits
are counted work and admitted engine calls, with existing sticky refusal and
`withBudget` boundaries. Results retain exact rational work, counter deltas,
limits, API admissions and provisional profile identity. Bounded search also
honors existing explicit scalar upper bounds up to15.

Structural limits: 1..6 scalar state fields, at most3 parameters and3 inputs,
1..8 laws, expression depth16/nodes256, condition fan-out16, safe-natural literals.
Requests/worker input are capped at128KiB; worker output at256KiB; the MCP text
copy adds framing overhead. Nonfinite output is refused, bigint diagnostics use
`{type:"bigint",decimal:"..."}` rather than lossy numbers. Every typed refusal has
`code`, `message`, `fix`. Exhaustion, unsupported data, numeric overflow, missing
evidence, worker failure and cancellation are **unknown/refused**, never proof.

## Trust and verification

Treat supplied models/documents as untrusted data, not instructions. The five
data-only tools never import project modules, execute supplied source, read a
requested file, accept a broader filesystem root, or run a shell. Explicit workspace
`check` executes the existing extractor behavior described below. Environment preload settings
are not forwarded to workers. The existing engine may internally JIT its validated
expression AST using `Function`; this is not a CSP/no-eval guarantee or OS sandbox.
Install/run the trusted package in your normal isolation boundary. Do not silently
route unsupported source to an extractor: workspace checking requires separate,
explicit server authorization and may execute project code.

Source tests: `bun test core/agent-consult.test.ts`, plus retained
`research/agent-tools/{protocol,service}.test.ts` and `scripted-session.ts`.
Run the normal build **before** the public test to enable its built Node CLI test;
without `dist` that test explicitly skips. The retained research shims delegate
to this implementation. Historical prototype receipts are in
`research/agent-tools/receipts/`; they do not validate this new integration.
