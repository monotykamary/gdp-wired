# Security mutation benchmark

A small **owned synthetic corpus**, not a CVE scanner or an estimate of real-world vulnerability recall.
The ten complete modules derive from the security feature's training shapes and exercise permission checks,
role checks, tenant-scoped writes/deletes and private reads, workflow prerequisites, quota admission,
payment deduplication, locks, transaction scope and atomic compare-and-set.
No third-party target is fetched or probed. Every accepted policy is stated in its source as `gdp: law`.

## What is measured

`run.ts` discovers all fixture directories and applies every eligible operator in `operators.ts`:

- **remove-guard**: delete an operation's early-return guard;
- **invert-guard**: negate that guard's predicate;
- **wrong-key**: replace a map-call key with another same-typed method parameter;
- **relax-boundary**: change `>=` to `>` in an early-return guard;
- **weaken-isolation**: change a Python `gdp: env atomic`/`snapshot` deployment declaration to `read committed`;
- **remove-lock**: remove a one-permit lock wrapper while retaining its operation statements;
- **narrow-transaction**: move a transaction's leading store read outside its atomic scope;
- **split-compare-set**: split an atomic scalar `modify` returning `[success, nextValue]` into read-then-write.

The source-level operators recognize canonical Effect/TxRef syntax structurally. They do not recognize
particular variable names or select a different mutation for a particular fixture. The source operations
remain executable TypeScript; the compare-and-set uses conditional `TxRef.modify`, not a mocked CAS primitive.

Each mutant changes one contiguous source span. Operators never inspect file names, policy names,
fixture IDs or verdicts. They do not remove laws or mutate constructor validation. All generated
mutants remain in the denominator, including any future survivor, refusal, timeout or equivalent mutant.
This release happens to have a concrete counterexample for each generated mutant; that is not a claim
that every application of these operators always introduces a security bug.

Both sides use `check(..., {security: true, propose: false, ms: 8000})`. The clean module is checked once
per worker, then all its mutants, with unchanged budgets. A worker is isolated on a large boat VM.
No timing improvement is claimed. `--security` proposals remain review-required and are **not** treated
as accepted policy or counted as vulnerabilities/false positives.

A detection requires all of:

1. Both complete modules are read and checked against source; no unread accepted laws.
2. A stated law is refuted with a nonempty reachable run, with the same named policy on its clean parent.
3. That run executes on the actual mutant code and violates the policy on the concrete states.
4. The same requests execute on the clean parent and do not violate it; no clean stated law is refuted.

`replay.ts` imports the original TypeScript module, constructs its class and calls its methods.
It interprets the stated policy over actual before/after states, independently of the extracted transition
model. This interpreter supports the corpus's primitive values, maps, old-state references and universal
map quantifiers; other syntax refuses replay. Step-law scope, argument signatures, malformed traces and
safe-integer limits are checked. Source-state snapshots, full runs, hashes and both replay outcomes are
retained in `measurement.json`.

`verify.ts` regenerates **every** mutant and replays the saved witnesses without running the prover.
It rejects missing/duplicate fixtures or mutants, changed source/configuration hashes, admission-score
drift and any difference from the saved concrete replay receipts. The unit suite repeats this verification.

## Private reads and source-level concurrency

For `isolated by tenant seeing result`, `replayIsolation` creates two real objects: one receives every request,
the other only the selected tenant's. It compares the result of **every** request by that tenant, not just the
final state. The concrete owner is retained alongside the CLI's encoded owner ID so saved replays do not depend
on a later process's string-interning table.

`replay_effect.ts` runs the original operation bodies on Effect's runtime. Its instrumentation adds scheduling
gates between outer operations and exposes existing refs for observation; it never inserts a gate inside a
lock or transaction. This reproduces the exact counterexample's fiber/step schedule. The clean parent's changed
atomic boundaries cannot execute an illegal mutant schedule, so its same calls are explicitly projected onto
serial execution under its real boundaries.

A separate `native_effect.ts` regression removes **all scheduling gates** and runs those calls concurrently
using only Effect's native `Scheduler.MaxOpsBeforeYield = 32`. All three source-level races also reproduce there;
clean counterparts remain safe. Only observation of existing refs remains. This guards against inventing a race
by instrumentation. Native checks run in child processes with hard deadlines. The uniform native scheduler
setting is not a prover budget or a per-fixture parameter.

The source-level probes exposed a CLI defect: concurrent counterexamples were printed as repeated ordinary
calls, dropping fiber identity and step boundaries. The CLI now preserves both, while retaining decoded input
values. The existing `gdp-wired/effect` `fiberRun` export is preserved; its pure formatter lives separately so
Python-only CLI use does not acquire an optional TypeScript-reader dependency.

## Isolation and trust boundaries

The race is an explicit **deployment-isolation mutation**, not removal of a source-level transaction API.
The Python method body is unchanged. Under `read committed`, its two calls can both read the missing
payment marker before either commits; both invoke the actual declared effect. `replay_race.py` drives
those source calls with deterministic cache read/commit barriers. Under the parent's `atomic` contract,
the same requests are serialized and only one effect occurs. This is **source replay under the model**,
not a replay against a real database or a claim about unmodelled isolation mechanisms.

A projected-away effect payload may be absent from a printed witness. The Python replay completes only
primitive annotated/defaulted arguments, records each value in `completedArguments`, and runs that
concrete completion on both sides. Missing untyped inputs refuse replay; nothing is guessed silently.

Permission and tenant inputs represent values already resolved by an authentication boundary. The laws
do not establish that boundary's trustworthiness, nor do these small modules prove whole-app security.
The tenant policies cover insertion, update and deletion, including deletion of a foreign zero-valued row.
This corpus does not measure unsupported languages, real database races or upstream CVEs.

## Reproduce on boat

From the repository root:

```sh
supercomputer run --jobs research/security/mutants/jobs.json \
  --out runs/security-mutants --class gate --timing --vm-type large
# Small local receipt collection; refuses incomplete or mixed-harness batches:
bun research/security/mutants/collect.ts runs/security-mutants \
  research/security/mutants/measurement.json
```

To replay the committed witnesses or run tests, put these commands in a supercomputer job
(starting with `bun install --frozen-lockfile`):

```sh
bun research/security/mutants/verify.ts research/security/mutants/measurement.json
bun test research/security/mutants/mutants.test.ts
```

For one module, `bun research/security/mutants/run.ts permission` emits one `MUTATION_RESULT` JSON line.
The full checked-in jobs file runs all modules; do not report a selected subset as whole-corpus recall.
See [RESULTS.md](RESULTS.md) for the measured table and validation receipts.
