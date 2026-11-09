# Prove in CI, ship plain code

Install `gdp-wired` and TypeScript as **dev dependencies**. The default deployment pattern has no prover in the application dependency graph:

```sh
npm install --save-dev gdp-wired typescript
npx gdp-wired-cli check src/policy.ts --mode standalone --entry decide --no-propose
```

## First choice: prove the plain source

A supported standalone decision needs no duplicate `*.model.ts`:

```ts
// src/policy.ts — no library import, safe to ship by itself
// gdp: law disabled refuses: not enabled implies not result
// gdp: law unready refuses: not ready implies not result
export function decide(enabled: boolean, ready: boolean): boolean {
  if (!enabled) return false;
  return ready;
}
```

Use `--entry` to choose the function and `--mode standalone` to select the pure-function reader. For a file with laws on several functions, omit `--entry` so the CLI checks every annotated decision: explicitly selecting only one does not silently suppress the other stated laws and therefore returns exit 2 for those left unread. The reader accepts a deliberately bounded subset, checks its extracted machine against concrete executions, and sends stated laws to the existing kernel-checked prover. A successful check is not a promise that arbitrary TypeScript, dependencies, or surrounding application code were verified. A refusal is not a pass. CI must reject exit 1 (broken law) and exit 2 (not checked).

Early-return decisions over booleans and string-literal unions, comparisons of comparisons, and string-union or nullable scalar results are useful cases for this path. Unsupported effects and code outside the closed function boundary are refused rather than ignored. Put one function's laws immediately above that function. Multi-step protocol models describe flows and remain separate tests: proving an individual decision does not prove that its callers enforce the right order.

## Fallback: keep the model only in tests

For source outside the reader's subset, write a model beside the tests, prove its laws, and test the production function against that model. Neither the model nor the prover needs to ship.

```ts
import {bool, fun, proveDecision} from 'gdp-wired'
const model = fun('permit').inputs({enabled: bool, ready: bool})
  .returns(({enabled, ready}) => ({permit: enabled.and(ready)}))
const law = model.law('disabled refuses', ({enabled}) => enabled.not(), out => out.permit.not())
const proof = proveDecision(law)
if (!(proof.proven && proof.checked)) throw Error('law not kernel checked')
```

Require **both** `proven` and `checked` in real tests; the separate variables make the assertions clear:

```ts
const verdict = proveDecision(law)
if (!(verdict.proven && verdict.checked)) throw Error('law not proven')
const result = model.compare(({enabled, ready}) => ({permit: enabled && ready}))
if (result.failure || !result.exhaustive || result.checked !== 4) throw Error('implementation differs')
```

### What exhaustive means

`fun.compare(reference, options?)` covers the finite input domain at the supplied fixed `options.params` tuple. Its receipt includes `parameterScope: {kind: "fixed", values: ...}` when parameters exist. `exhaustive: true` additionally requires finite parameter kinds; it never means other parameter tuples were tested. It counts **input cases**, not fields. `bool`, `oneOf`, `upTo`, finite records, finite variants, and optional finite kinds can be enumerated. A matching four-case decision returns `{checked: 4, exhaustive: true}`. The first disagreement includes its input values.

`rule.compare({init, step}, options?)` also enumerates finite parameters and request inputs. Its finite traversal checks input combinations in bounded sequences, resetting after `depth` requests. **It does not enumerate all histories, all reachable states, or arbitrary externally supplied state.** A request-dependent decision and a protocol invariant are different claims.

Unbounded kinds, custom draws/parameter generators, or domains above `maxCases` (100,000 by default) fall back to sampling, with `exhaustive: false`. A skip because an assumption rejects an input is reported separately and does not claim full coverage. Explicit edge cases augment the test. Reference functions must be deterministic; they are not trusted proof steps.

**Even an exhaustive comparison is a test, not a proof.** The kernel proves a model's stated laws. Comparing that model with hand-written code gives evidence of agreement over the reported inputs; it does not extend the kernel's trusted base or certify the rest of the application.

## Optional runtime use: interpretation unless compilation is explicit

Shipping plain code remains the recommended CI-only pattern. If a model is deliberately included at runtime, `fun(...).run(inputs, params?)` now interprets its terms. The encoded inputs, decoded output kinds, assumptions and exact-integer checks are unchanged. The model and runtime are cached, but each call starts from its own initial state.

Generated JavaScript is an explicit opt-in:

```ts
import {bool, fun} from 'gdp-wired'
const decision = fun('permit').inputs({ready: bool}).returns(({ready}) => ({ok: ready}))
const run = decision.compiled() // uses dynamic code generation: not for restrictive CSP
console.log(run({ready: true}))
console.log(decision.run({ready: false})) // interpreted; no dynamic code generation
```

**Migration:** code that relied on `.run()` compiling declared `.fns(...)` helper source must instead call `.compiled()` once and use its returned callable. This includes string helpers and callback helpers, because the existing helper machinery serializes callbacks to source. The default refuses such helpers **before** machine construction; it does not silently invoke `Function`. Native term arithmetic (`n.divBy(2)`, `n.modBy(2)`, rounding helpers), library `divBy`/`modBy` helpers and `recur` equations with only source-free dependencies all work with the default interpreter. They retain serializable direct implementations, so materialization and interpretation do not compile their generated JavaScript. A recurrence that transitively calls user JavaScript still needs the explicit opt-in. `rule.compiled()` remains an explicit opt-in. `rule.interpreter()` also refuses declared helper source before materializing the machine; deliberately allow it with `rule.interpreter({compileHelpers: true})`. Library-produced direct metadata is a trusted model representation, not provenance or a proof that manually forged metadata matches arbitrary JavaScript. Ordinary source/arity overrides or changed descriptors invalidate native dispatch; they do not silently keep an old implementation. This is not a claim that all proof APIs, low-level machine helpers, extraction tools, or `compare()` are CSP-safe: these are CI/tooling paths and may compile code.

Measured before selecting this default, on one exclusive large AMD Ryzen 9 9950X VM with two vCPUs: the three 4/128/32-input decisions took approximately **1.71 / 2.86 / 1.82 μs per call interpreted**, versus **2.28 / 3.28 / 3.10 μs compiled** with the existing wrapper; plain TypeScript took **0.021 / 0.037 / 0.031 μs**. The measurement includes encoding/decoding and adapters (100,000 warm calls, 1,000 cold creations); it is not an isolated evaluator benchmark or a universal performance guarantee. Plain application code remains far cheaper. The selected default removes dynamic compilation without a measured wrapper-level regression on these decisions.

## Mutation checks: test whether the law suite catches a regression

Create a trusted JSON configuration, for example `test/mutants.json`:

```json
{
  "cwd": "..",
  "lawSuite": "laws",
  "suites": [
    {"name": "examples", "command": ["bun", "test", "test/examples.test.ts"]},
    {"name": "laws", "command": ["bun", "test", "test/laws.test.ts"]}
  ],
  "mutants": [
    {"name": "ignore-ready", "file": "src/policy.ts", "from": "return ready;", "to": "return true;", "bug": "an unready request is admitted"}
  ]
}
```

Run `npx gdp-wired-cli mutate test/mutants.json` (or `gdp-wired mutate ...` when installed locally). Paths are relative to the configuration's directory plus `cwd`, not the shell's current directory. The command prints `mutant | bug | suite...` in Markdown; `--json` includes bounded suite output and exit receipts. Exit 0 means every mutant was caught by the designated law suite and no suite had an infrastructure error; exit 1 means a survivor or error; malformed configuration or a failed baseline exits 2.

The same operation is available from the separate `gdp-wired/mutate` subpath (Node.js 20.16+ or Bun on POSIX, with `ps` available; Windows is currently refused):

```ts
import {checkMutations} from 'gdp-wired/mutate'
const config = {cwd: process.cwd(), lawSuite: 'laws', suites: [{name: 'laws', command: ['bun', 'test', 'test/laws.test.ts']}], mutants: [{file: 'src/policy.ts', from: 'return ready;', to: 'return true;', bug: 'ignores readiness'}]}
const result = checkMutations(config)
console.log(result.markdown)
if (!result.passed) process.exitCode = 1
```

The runner preflights every edit, requires exactly one `from` match, rejects source symlinks and no-op edits, verifies every suite passes **unmutated**, then applies each edit separately. It restores the exact original bytes in `finally`, even on a command error or timeout. Each suite has its own POSIX process group; remaining members are enumerated and stopped by exact PID before restoration, including on timeout. A timeout, missing executable, signal, output-overflow, or failed process cleanup is **not** a caught mutant. Commands are argv arrays, never generated shell strings. The default timeout is 120 seconds per suite (`timeoutMs` changes it), with bounded output.

Only run configurations you trust. They execute commands with your privileges. Use a disposable checkout, never concurrent mutation runs on the same source. Commands that deliberately escape their process group, external concurrent writers, SIGKILL of this runner, machine failure, or loss of filesystem access are outside the restoration guarantee. This is process supervision, not a sandbox. For pure scalar decision terms, `deriveDecisionMutants` generates bounded candidates that negate a guard, drop a conjunct, flip a comparison, or widen a choice. Supply legal numeric choice encodings to enable widening; the generator does not guess a domain from literals. Supply a trusted deterministic `render(machine)` that prints the implementation artifact your suites actually execute. Both the original and each mutated machine use that same printer. This is an explicit source bridge, **not** an automatic inverse mapping to arbitrary hand-written TypeScript. The resulting ordinary source edits go through exactly the same preflight, baseline and restoration checks:

```ts
import {bool, fun} from 'gdp-wired'
import {deriveDecisionMutants} from 'gdp-wired/mutate'
const f = fun('permit').inputs({ready: bool}).returns(({ready}) => ({ok: ready}))
const mutants = deriveDecisionMutants(f.rule.machine, {file: 'decision.ts', render: m => `export default ${JSON.stringify(m)}\n`})
console.log(mutants.map(m => m.name)) // pass these edits to checkMutations with your suites
```

The default cap is 64 candidates (`maxCandidates`: 1–1000). Identical emitted variants are deduplicated. Only step flags and output expressions change; assumptions, preconditions, initial state and law facts are not mutated. Stateful, map/helper, history and quantified terms are refused. Candidates may be equivalent or survive: the generator never claims that every candidate is a bug. Add a named suite for each law plus a designated aggregate law suite to make the normal Markdown columns show exactly which laws kill each variant. Source restoration still happens after all suites for each candidate.

## Package and maintenance posture

The `gdp-wired` library has no runtime dependencies and no install lifecycle scripts. Its optional TypeScript and gdp-ts peers are needed only for the integrations that use them. The separate **CLI convenience package** `gdp-wired-cli` deliberately depends on `gdp-wired` and TypeScript; it is tooling, not a zero-dependency runtime library. Source-language toolchains may also be required for source replay.

The release workflow uses npm Trusted Publishing/OIDC and publishes with `--provenance`. Provenance records where a package was built; it is not a security audit and does not eliminate maintainer risk. Pin versions and lockfiles, review updates, and keep the tooling in CI when runtime inclusion is unnecessary.

Addressing a single-maintainer concern requires governance beyond code: an organization-owned repository/package, a second authorized publisher and reviewer, protected release branches/environments, documented recovery and succession, and independent review. Ownership and publishing credentials must be changed by the maintainers—not by an automated code change.
