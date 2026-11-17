# Workspace `check`

Use `check` to read laws from a trusted Python or plain TypeScript/JavaScript
workspace through the same engine as the CLI. The default remains data-only;
filesystem access requires explicit server configuration.

The native edit/check fixture exercises both Python and TypeScript through the
built Node MCP server: a bounded implementation is proven, a conservative edit
remains proven, and a bad edit is broken with a real run. These results retain
`translation: sampled`; they are not exhaustive native equivalence certificates.

## Server-owned authority; data-only default

`createConsultation()` and the stdio executable with no root configuration keep
the old data-only default. All six tools are listed; `check` returns the typed
`workspace-unconfigured` refusal until the server explicitly opts in:

```ts
import {createConsultation} from 'gdp-wired/agent-consult'

const session = createConsultation({workspaceRoots: ['/absolute/trusted/project']})
const receipt = await session.call('check', {
  file: '/absolute/trusted/project/counter.py',
  budget: {work: 5000000, apiCalls: 64, candidates: 2}
})
```

For the stdio server, the operator sets `GDP_AGENT_CONSULT_ROOTS` to a JSON array
of absolute directories in its startup environment. CLI arguments still cannot
choose roots, source modules, flags or interpreters. Root configuration is never
accepted in tool arguments, including nested `options`, `root`, `roots`, `python`
or `workspaceRoots`. The existing five tools remain data-only.

The server canonicalizes/freezes at most16 roots once. Requests must name absolute
local regular files (no URLs, directories, devices, relative paths or `..`).
Containment uses `path.relative`, not a string prefix. Both root and file symlinks
are realpathed; out-of-root results and sibling-prefix paths are refused. Source
reads used by the guard use a no-follow/nonblocking read-only FD and fstat; each
file is capped at128KiB. Root dev/inode and file identity/content are rechecked
before/after the pipeline; source and relative TS dependency hashes bind the
returned revision. Replacements or edits observed during a check refuse rather
than silently bind another revision.

**Not an OS sandbox:** the configured root is a trust grant to execute the existing
extractor/runtime/project code. Python may import dependencies; TypeScript native
replay may execute code. Those runtimes can read dependencies and access resources
outside the root with the worker's OS permissions. No claim of transitive import
confinement, hostile-code containment, or atomic filesystem snapshots is made.
An adversarial process can race mutable files between rechecks. Use a stable,
trusted checkout and externally enforced OS isolation for untrusted code. Cancellation
joins the direct worker; this is not a descendant-process sandbox/reaper guarantee.
No arbitrary shell launcher is added; only the installed fixed-path worker runs.

## Shared engine, explicit initial scope

`packages/cli/bin.js` delegates to `core/cli.ts`. The latter now has one generator
pipeline for entry enumeration, initializer expansion, laws, proof/replay and
proposals. Ordinary CLI calls drive it asynchronously; workspace check preloads
Python/plainTS extractor modules as initialization and then drives that **same**
pipeline synchronously inside the counted root. No copied extraction/proof engine
and no `withBudget(Promise)`.

Supported initially: Python and plain TypeScript/JavaScript (`.py`, `.ts`, `.mts`,
`.tsx`, `.js`, `.mjs`). Effect/XState, async lemma expansion and other CLI language
frontends are explicitly refused. The initial workspace profile does **not** read
project GDP configuration: no ancestor search, no config-specified interpreters,
root overrides, certificate writes or CLI switches. Ordinary CLI defaults/config
behavior remain unchanged. Rules needing config receive the extractor's refusal
or unknown rather than substituted modeling choices.

The returned `result.rules` is the existing structured CLI `RuleOut[]`: stated
laws, refusal reasons, replayed runs where available, and proposals with paste-ready
language comments in `where`. `proven` requires a nonempty stated law set all
reported proven by that engine; `broken` requires a stated broken law with a real
run; otherwise the aggregate is `unknown` with a reason. Each rule/law retains its
own detailed verdict. `check` does not populate the scalar-model `status` registry.

**Evidence boundary:** a model-only result with `translation: unchecked` remains
unknown even when `kernelProven: true`. When the existing engine supplies a native
law journal, its `sampled` or `exhaustive` profile and observation count are retained.
The current Python/TypeScript demo uses sampled journals. A checked symbolic proof
plus sampled native observations does not establish universal source equivalence.
This adapter neither upgrades unchecked results nor invents counterexample runs.

## Budget coverage

One `withBudget` root and sticky capacity-refusal boundary surround synchronous
extraction, law parsing, proofs, replay, proposals, source receipt construction and
serialization validation. Each extraction and top-level proof/step/liveness/two-run
API call is admitted against `apiCalls`. API exhaustion is also sticky, so existing
CLI catch-and-return-unknown handlers cannot turn exhaustion into a successful
partial proof receipt. Proposal candidates are finite and capped by the request
hint (at most40); CLI wall-clock stops/telemetry are disabled only for this counted
synchronous path. Ordinary CLI wall behavior is unchanged.

Exact work/counter deltas and profile identity are retained. Counted work means
**existing engine sinks**, not CPU instructions: module initialization, filesystem
bytes/identity/hash operations, unmetered frontend parsing, external interpreter
runtime and project execution are not charged to the work vector. Source-byte and
API caps are separate controls. These exclusions are explicit in every source
budget receipt; external runtime is not misrepresented as counted work.

## Development checks

After normal dependency preparation, run these checks in the project's test environment:

1. `bunx tsc -p core/agent-consult/tsconfig.json --noEmit`
2. `GDP_WORK_FULL=1 bun test core/agent-consult/workspace.test.ts core/agent-consult.test.ts research/agent-tools/protocol.test.ts research/agent-tools/service.test.ts`
3. The existing CLI, budget ownership, watchdog and package regression suites.
4. `bun scripts/build.ts`
5. `node scripts/agent-consult-workspace-demo.mjs > "$SUPERCOMPUTER_OUTPUT_DIR/workspace-check-transcript.jsonl"`

The last command creates temporary Python and TS files, initializes/lists the
built Node MCP server, edits each through good/good-edit/bad versions, and logs
actual edit/request/response/observation JSONL. It requires successful extraction,
changing source revisions, sampled native-law observations for the good edits,
and real runs for the bad edits. The server must close cleanly after stdin EOF.
The workspace suite is also registered in the default CI test roster.
