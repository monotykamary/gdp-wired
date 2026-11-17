# Agent consultation 0.50.4 release candidate

The parent-owned installed-tarball gate has now passed. See
[the qualification receipt](agent-consult-packed-check.md). Main has reserved
`0.50.4` after `0.50.3` and notified bapa; the canonical exact-final-SHA release
gate remains outstanding.

## Reserved release version

Main reserved `0.50.4` for the six-tool agent-consult release and notified bapa.
This is the coordinated `0.50.4` release candidate: both package versions and the
CLI exact dependency were updated together, and the reviewed changelog entry is
under `0.50.4`. Main owns final acceptance and publication sequencing. A prepared
candidate is not permission to push, tag, publish or issue a GitHub write.

The coordinated `0.50.4` release cut uses `scripts/version.ts` to update the root
version, CLI version and CLI's exact `gdp-wired` dependency together. Final gates
run only after the release owner freezes the resulting source SHA. The MCP `serverInfo.version` is a separate protocol
implementation version, not the npm package version; this change does not alter it.
No model identifier changes are needed.

## Adapter decision

Retain the existing pure-Node newline-delimited JSON-RPC/MCP adapter and public
`gdp-wired/agent-consult` library. No MCP SDK dependency is needed to package the
six existing tools; adopting an SDK now would change the validated transport and
add release risk without providing a required capability. Node >=20 runs the
five data tools. Workspace checking also needs TypeScript beside the package and
Python for Python sources. No model credentials/provider or new native engine.

## Parent-owned packaging admission

The canonical `agent-consult-release` job in `supercomputer/suite.json` chains
strict typechecking, the build, counted-work focused tests, and the bounded
installed-package gate. This adds a release obligation without replacing or
changing any previous canonical job.
It installs frozen build dependencies, builds normally, **npm packs both paired
packages**, hashes/retains the tarballs, and installs those actual bytes plus
TypeScript 5.9.3 into a new `/tmp` consumer outside the checkout. Installation
scripts are disabled. npm may access its registry for TypeScript; no publishing
or GitHub writes occur. The native worker must provide Node >=20, npm, Bun,
TypeScript installation access, Python 3, GNU timeout and sha256sum. Main submits
only after its normal admission process, at the reviewed commit; this author has
not run the job or any install/build/test/prover.

The copied consumer imports only the public package subpath and launches only the
installed `.bin/gdp-wired-agent-consult` command. Both modes list and exercise all
six tools, require checked scalar proofs, real traces, checked support sets and
status without invented native evidence. Each mode writes and edits Python/TS
through good/good-edit/bad versions, requires sampled native observations and real
counterexample runs, and checks changing revision digests. It also checks default
root refusal, sibling-prefix/symlink escape, traversal, relative/URL/directory
refusals, caller-root injection, zero work/API budgets and package version linkage.
A missing-installed-worker fault injection must yield `worker-failure`, not a
source-checkout fallback. Only the installed copy is modified, then restored.
The wrapper's installed public bin is exercised with `--help`; the consumer is
also typechecked against the installed declarations. No source/dist entrypoint
is directly executed. Installed resolution/bin realpaths must be inside the
fixture's node_modules. Preserve the JSONL transcript, stderr, package tree,
version/toolchain logs, pack metadata and tarball hashes. Timeouts/nonzero/missing
artifacts are unresolved failures, never evidence of success; no automatic retry.

Existing core evidence supplied by Main: four native gates `045855-xlfv91` and
docs gate `050246-iwrjlf`. Do not rerun those merely for this packaging prep.
The historical packed-consumer qualification does not replace the exact-final-
SHA canonical release gate or privacy review required by
`scripts/release-ci/FULL-GATE.md` and `.github/workflows/publish.yml`.

## Trust limitations (keep in release notes)

The five model tools accept data, not project modules. Workspace `check` is a
separate, explicit server-owned roots opt-in. Root checks guard requested file
identity/containment, not runtime resources: the existing extractor can execute
trusted project code/imports with worker OS permissions, including outside-root
access. This is not an OS sandbox, transitive import confinement, atomic snapshot
or descendant-process containment guarantee. Use stable trusted checkouts and
external OS isolation for untrusted code.

Python/TS journals here are **sampled**, not exhaustive source equivalence.
Unchecked translation stays unknown even with a symbolic kernel proof. Counted
work uses provisional existing-engine sinks, not CPU instructions; initialization,
filesystem/hash work, unmetered parsing, interpreter runtime and project execution
are excluded. Source-byte/API caps are separate; candidate/sample limits are
hints, not hard bounds on every operation. Exhaustion/cancellation/refusal is not
proof; `ok` alone is not proof. Keep per-law checked proof pairs and native
observations distinct. No inference engine, model identity or proof scope changed.
