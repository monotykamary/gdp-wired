# Agent consultation MCP (research prototype)

Branch `feat/agent-consult-mcp`. **No broad promotion before the surface-semantics
release gate.** This is a thin stdio adapter, not a new reasoning engine.

## Run

```sh
bun research/agent-tools/stdio.ts
```

No installation or network access is required. The process reads newline-delimited
JSON-RPC2.0 MCP on stdin and writes only protocol JSON to stdout. It supports
`initialize` (2024-11-05), `tools/list`, `tools/call`, and `ping`. Tool results have
both compact `structuredContent` and a JSON text block for older MCP clients.

A generic client may register `{ "command": "bun", "args": ["/absolute/path/to/research/agent-tools/stdio.ts"] }`.
This does not modify any agent's configuration. Input schemas describe all fields.

## Data and tools

`subject` is `{unit, rule}`; `rule` is existing scalar-natural Machine JSON:
`name`, `params`, `inputs`, initial `state`, `step.state`, optional `pre` and
`assume`. Terms: `var`, `const`, `add`, **truncated natural `sub`**, `min`, `max`,
constant `mul`, `if`. Conditions: `<`, `<=`, `=`, `and`, `or`, `not`. A law is
`{name, holds}`. Signed integers, maps, functions, quantification, callbacks,
source strings, filesystem paths and network URLs are refused, not approximated.
The example documents are in `examples.ts`; schemas are returned by `tools/list`.

- **prove** `{subject,laws,budget?}` calls existing `proveLaws`. Only the pair
  `proven:true, checked:true` receives the `proven` label. No native claim.
- **why_not** `{subject,laws,budget?}` calls existing interpreter-checked `search`.
  Traces have the code's parameter/input/state names. Minimality is length-first
  only inside the library's finite search domain (including explicit upper-bound
  overrides up to15). Absence of a trace is not proof of a law.
- **suggest** `{subject,laws,nearMisses?,budget?}` calls existing `inferLaws`, checks
  returned support sets jointly, and uses existing `search` to test the supplied
  near-miss candidates. It does not invent candidates through another engine.
  Returned laws include pasteable Machine/Law source and required support.
- **check_change** `{before,after,laws,budget?}` checks the same named laws on
  both revisions. Newly broken means an old checked proof plus a new reachable
  trace; inability to re-prove is separately reported as `lostProof`. Existing
  `compose.refinement/agree` compares matching state/input/parameter names;
  invariant **and** request-admissibility obligations must both be checked.
  The relation is directional, under the new implementation's precondition—not
  a claim of unrestricted bidirectional/source equivalence.
- **status** `{unit,revision}` uses only evidence from this server's computational
  requests, keyed by the exact rule-and-law digest. Caller-supplied labels are
  refused. Native `conformance` / `harness-checked` remain unavailable without
  trusted native evidence integration. Unknown units yield typed missing-evidence
  refusals; no old revision is silently substituted. The in-memory registry retains at most256 revisions (oldest entries are evicted); there is no persistent evidence database.

## Counted limits

Defaults: work500000, API calls24, search depth3, default value bound2, inference
candidate-pool hint64. `candidates` is the existing inference pool hint, not a hard bound on all candidates processed; `runs:128` is likewise an engine sampling hint. Hard limits are the counted work and admitted API calls; schemas also bound input size and finite-search depth/value range. Structural validation separately limits
size, names and AST depth. Each computational call starts a fresh local process
with the existing `GDP_WORK_FULL=1` profile, executes synchronously inside
`withBudget` + the existing sticky capacity-refusal boundary, and reports exact
rational work/counter deltas. No wall-clock budget or timeout is used as an answer.
The existing engine may internally JIT its validated expression AST using `Function`; this is not a CSP/no-eval guarantee. It never evaluates client-provided source text.
The existing raw-work profile is **provisional research machinery**; this wrapper
neither reprices it nor certifies its release. No client-provided code is imported.

Refusals always carry `code`, `message`, `fix`. Budget exhaustion is unknown, never
proof or counterexample. Output size and request size are capped. Nonfinite output is refused rather than coerced to JSON null; bigint diagnostics use an explicit `{type:"bigint",decimal:"…"}` encoding. The server kills
only its own exact child on termination; no background worker survives shutdown.

## Exercise

```sh
bun test research/agent-tools/protocol.test.ts
GDP_WORK_FULL=1 bun test research/agent-tools/service.test.ts
bun research/agent-tools/scripted-session.ts --out /tmp/agent-session.json
```

The first command is a tiny local data-only check. The scripted agent session
uses real stdio tools on two rule families (budget and permit slots), introduces a
broken revision, checks proofs/traces/suggestions/status, tests exhaustion and
checks deterministic replay and forces counted/API exhaustion. The permit accounting variant also requires genuinely inferred helper `held + released <= acquired`, checked jointly with the requested law. A unit test replaces wall clocks with throwing functions; overflow must produce a typed refusal. It is scripted, not an LLM/network session.
The ordinary interactive `dev.jobs.json` is the **dependency-free runtime loop**:
it runs unit tests and the scripted MCP session using the already available Bun.
It does not install packages or run full-project static checks. Use
`verify.jobs.json` separately for frozen dependencies, the focused strict type
check, commitlint and runtime checks. Neither is strict-once. See `RESULTS.md`
for inspected receipts; this is not a release or native-parity acceptance gate.
