# CI-first-class track

Gate: **PENDING**. Branch `claude/ci-first-class`; starting revision `b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`. No merge/push/release is authorized.

## Item 0 — plain-file decision laws

**Starting status: partly.** `core/extract-standalone.ts:93-97` already walks binary expressions, returns, and if chains, but its expression whitelist omits string and null literals. `core/extract-shapes.ts:346-382` requires opt-in standalone mode and accepts only numeric/boolean inputs and results; null results are explicitly refused. Implemented finite string/record inputs, early-return predicates, nullable choice results, result-field laws and cross-domain choice equality. Whole-file Boat replay now proves all 20 per-input laws with exit 0 (13 + 7); the protocol laws remain models, not extracted implementation proofs. Synthetic regression coverage and the standalone CLI tests passed.

## Item 1 — exhaustive comparison

**Starting status: partly.** Both `rule.compare` (`core/dsl.ts:2293`) and `fun.compare` (`core/dsl.ts:2494`) already exist; the latter is not missing. Both currently sample and increment `checked` per output field, return no `exhaustive` flag, and have no finite-domain enumeration. Finite kinds already expose their shape in `core/dsl.ts:361-633`. Implemented finite-domain traversal with an up-front 100,000-case guard, sampling fallback, case counts, first-disagreement inputs/trace, reference isolation, and explicit skip accounting. Both function and rule APIs expose `exhaustive`; rule coverage is bounded traversal, not exhaustive state-history coverage or a proof. The comparison regressions passed in the 61-test v4 focused suite.

## Item 2 — built-in mutation check

**Starting status: missing.** `core/cli.ts:843-859` dispatches only `check` and `draft`; `package.json` has no mutation subpath or script. The existing research mutants are corpus-specific, not a source-edit/suite runner. Implemented `gdp-wired mutate` / `gdp-wired-cli mutate` and the separate Node-only `checkMutations` API. Preflight requires an unambiguous source match, unchanged baseline bytes, regular non-symlink files, and passing unmutated suites. Each mutant restores exact bytes in `finally`; timeouts, signals, missing commands and output overflow are errors, not kills. Markdown/JSON receipts and designated-law-suite failure are covered by the successful v4 focused tests. The automatic term-mutant stretch goal was subsequently implemented at the coordinator's request; see the follow-up section below.

## Item 3 — explicit runtime compilation

**Starting status: partly.** `Rule.interpreter()` and explicit `Rule.compiled()` already exist (`core/dsl.ts:2417-2420`), but `Fun.run` always compiles (`core/dsl.ts:2513-2521`). The interpreter itself compiles declared helper source (`core/machine.ts:351-371`), and building those machines validates helper source through compilation (`core/dsl.ts:1540-1544,2131`). Implemented the interpreter default after the successful actual-example measurement, with cached explicit `Fun.compiled()` callables. Declared helper source is refused before default-runtime machine construction; native arithmetic terms need no compilation. The v6 runtime/export probe passed 62 tests, and v7 passed check, lint, build and 28 built-package/runtime tests. Detailed timings and migration notes are below.

## Item 4 — CI-only docs and package posture

**Starting status: partly.** The README leads with runtime installation (`README.md:17-19`); the skill recommends shipping compiled rules (`skills/gdp-wired/SKILL.md:67-70`). The library already has no runtime dependencies and no install lifecycle hooks (`package.json`); only dev dependencies and optional peers. The separate CLI wrapper deliberately depends on the library and TypeScript (`packages/cli/package.json:27-30`). `.github/workflows/publish.yml:43-45,149` already uses OIDC and `--provenance`. Registry metadata confirmed by bounded read-only GETs on 2026-11-09 UTC: [library 0.47.0](https://registry.npmjs.org/gdp-wired/0.47.0) has neither dependencies nor optional dependencies, and has only `prepublishOnly`, not install lifecycle hooks; [CLI 0.47.0](https://registry.npmjs.org/gdp-wired-cli/0.47.0) has the two expected tooling dependencies and no scripts. Both advertise npm SLSA provenance attestations ([library](https://registry.npmjs.org/-/npm/v1/attestations/gdp-wired@0.47.0), [CLI](https://registry.npmjs.org/-/npm/v1/attestations/gdp-wired-cli@0.47.0)). This confirms registry posture, not an independent cryptographic audit. Added explicit CI-first README/skill/shipping guidance, `docs/ci-only.md`, release migration notes and package-posture regressions. The focused source/built export tests pass; no ownership, dependency, version or publishing configuration was changed.

## Execution notes

- All builds, tests, experiments, and timings run on Boat through `supercomputer`. Laptop work is file inspection/editing, Git, and remote controllers only.
- Initial item-0 worker failed authentication before doing the experiment; restarted with an authenticated, exactly selected model.
- Initial submodule initialization refused the repository's preconfigured local-file transport. Retried with command-scoped `-c protocol.file.allow=always`; no global Git settings changed. Both pinned submodules now initialized successfully.
- Validation infrastructure failures: initial mutation and health submissions failed before execution in `scheduler.store_blobs` (`ValueError: blob bytes do not match their key`). A pre-existing bounded runtime retry program timed out two further Boat submissions and its Modal fallback then refused a changing `.pi/fabric/mesh/state.json`. No timing or test pass is inferred from these failures. Added `.pi/**` to upload exclusions for future runs. The coordinator diagnosed laptop memory pressure and blob-cache lock contention, limited this lane to one subagent, and directed that existing Boat submissions be left alone. Extra agents were stopped/closed; no further resubmission is being made under that instruction. No other client or shared scheduler process was stopped.
- Customer files are read-only; copies and their experiment outputs stay in private scratch directories outside repositories. Public fixtures are independently written synthetic decisions.

## API review examples (candidate code; validation pending)

`Fun.compare` (existing API, now finite input coverage):

```ts
import {bool, fun} from 'gdp-wired'
const f = fun('permit').inputs({a: bool, b: bool}).returns(({a, b}) => ({ok: a.and(b)}))
const result = f.compare(({a, b}) => ({ok: a && b}))
if (result.failure || !result.exhaustive || result.checked !== 4) throw Error('mismatch')
console.log(result)
```

`Rule.compare` (existing API, now finite parameter/input coverage, not every history):

```ts
import {bool, rule} from 'gdp-wired'
const r = rule('switch').inputs({on: bool}).state({value: bool.from(false)}).step(({on}) => ({value: on}))
const result = r.compare({init: () => ({value: false}), step: (_p, _s, {on}) => ({value: on})})
if (result.failure || !result.exhaustive || result.checked !== 2) throw Error('mismatch')
console.log(result)
```

`checkMutations` (new Node-only subpath API):

```ts
import {checkMutations} from 'gdp-wired/mutate'
const result = checkMutations({lawSuite: 'laws', suites: [{name: 'laws', command: ['bun', 'test', 'policy.test.ts']}], mutants: [{file: 'policy.ts', from: 'return ready;', to: 'return true;', bug: 'ignores readiness'}]})
console.log(result.markdown)
if (!result.passed) process.exitCode = 1
// Equivalent CLI: gdp-wired mutate mutants.json (paths relative to the config directory).
```

## Maintenance recommendations

An organization-owned repository/package, a second authorized publisher and reviewer, protected releases, documented account recovery/succession, and independent review address the single-maintainer concern beyond code. Keep the prover in dev dependencies and pin reviewed versions/lockfiles. Provenance identifies build origin, not correctness or the absence of malicious maintainers. No ownership, npm publisher, release, tag, push, or GitHub write was changed by this track.

## Disk

Coordinator disk limits received: no new whole-tree archive per run; future source archives will be created once, only at `/private/tmp/gdp-archives/<sha>.tar`, and reused via `--data`. No tree tar will be copied into an output/input directory. New result collection will request summaries, receipts and hashes; raw logs only for a specific diagnostic, compressed. No planned write exceeds 500 MB. No files were deleted.

2026-11-10 local inventory: this checkout's `runs/` uses 70 MB; `/tmp/gdp-ci-gate-inputs/` contains 15 MB of existing shared baseline Git packs, `/tmp/gdp-ci-probe/` 72 KB of fixed patch/control files, and `/tmp/ci-item3-private/` 36 KB of private benchmark controls. Laptop reports 31 GiB free. The 15 MB baseline pack directory predates this instruction; it is still used by active submissions, not a new per-run archive.

Deletion candidates for coordinator decision only: `/tmp/gdp-ci-gate-inputs/` (15 MB, duplicate transport material after all existing consumers finish and a canonical SHA archive is available); `/tmp/gdp-ci-probe/` (72 KB, superseded diagnostic snapshot after its receipts are captured); `/tmp/ci-item3-private/` (36 KB, private benchmark scratch after the runtime study completes). These are not safe to remove while their jobs/observers are pending. `runs/bar/trees/` (67 MB, immutable baseline worktree plus dependencies) is another candidate only after all baseline/probe consumers finish, and should be removed through `git worktree remove`, not manual deletion. No other lane's files were inspected for deletion.

## Newly diagnosed validation failure

The initial IC3Syn baseline batch `20261110-001629-nug8n1` completed with all seven jobs exiting 127 because `/tmp/ci-gate/setup.sh` was absent. The `supercomputer run` wrapper itself exited 0; this is **not** a gate pass. The attached data is shipped inside the source tree, not at an absolute `/tmp` mount (`boat.py:815–827` strips leading slashes from the destination). The same wrong absolute-path assumption affects the still-pending earlier probes. Corrected probe-v3 uses relative mounts and the existing canonical archives plus raw commit metadata to verify source tree and commit hashes before running tests. Existing probes are being allowed to finish; subsequent commands will use the verified relative data path. No census verdicts were produced by this batch.

## Corrected validation, first actual results

`runs/probe-v3` / batch `20261110-005350-3gjxur` restored an exact clean baseline: commit `b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`, tree `c46b265c960ff6b905bde5134844a175b40c12c9`, submodules `d47141cce2caf5b86b0c2c0c372a5174f424bc15` and `0b6ebeeec827b05210f3acfa4149a70dda9a0de5`. After applying the frozen candidate delta, installation passed. Focused tests: **53 passed, 8 failed**; typecheck failed on two readonly writes in a mutation-isolation test. The failures were a test fixture that enumerated extra builder environment fields, changed reserved-parameter wording, and an obsolete expectation that a nullable numeric result must be refused. Fixes are in the next snapshot; these results are not a green gate.

Corrected v4 work: focused tests and check/build (`7be49f30-8d14-4ae3-a64d-be3bd4059984`, `runs/probe-v4`); original published/source/final private-law table plus actual-example runtime measurements (`cd319e6f-d109-421e-9fba-6915542a3e8a`, private output `/tmp/gdp-ci-private-v4-results`); all 29 original baseline generation verdicts (`1d551c24-c89e-483b-a52b-f3ebe0a1987a`, `runs/main-census-v4`). Each has one active controller. Earlier absolute-path probes finished without testing candidate code and are not counted as passes.

The published-metadata job completed successfully (`runs/package-posture/published-metadata.log`), confirming the registry details above. The separate baseline-check job failed at its missing absolute data path.

Recovered synthetic runtime measurements are in `runs/item3-synthetic-baseline.json`: warm compiled/interpreter ns/op were 1525.7/1474.3 (4 inputs), 3206.5/2118.7 (128), and 2240.1/1620.0 (32). Cold model-create/first-call compiled/interpreter ns/op were 52336.7/16079.9, 59082.4/29587.6, and 53802.7/36660.4 respectively. These include encoding/decoding and wrapper overhead, on the exclusive large AMD Ryzen 9 9950X placement; they are not isolated expression timings. The requested private-example measurements still need to complete before choosing the public default.

## Main bar baseline recovery

The original full baseline controller is still completing its successful f1/f2/rw/suite groups; it is not restarted. Four other groups stopped during remote **task enumeration**, before any solver measurement: CHC/ITS/SV/TIP `/submit` calls timed out. A scheduler snapshot of CHC shows only the completed `call-tasks` enumeration row, not any prover jobs. These missing groups are retried separately after reconciling their old registrations; no successful solver measurements are repeated. Compressed original failure logs are retained in `runs/bar/infra-pilot-failures/`. The retried groups use the same immutable baseline and existing shared cache. No shared scheduler policy or foreign VM is changed.

## Coordinator-directed baseline stop

The coordinator directed that baseline bar work stop while main is expected to advance through the MLDR integration gate. Exact bar controller PIDs `75585` and `2147` received SIGTERM and exited 130; completed receipts remain intact. Scheduler verification found no remaining batches for either controller after closing their eight abandoned metadata-only registrations. The stale census controller also exited 130 and its batch and VM runs are gone. The stale baseline-only census batch `20261110-010529-6ckjrw` is also being cancelled to release gate capacity. No successful candidate gate is claimed. Focused checks, private-law replay and runtime measurements remain submission-class work. Before final gates, rebase onto the resulting main and make the candidate ready; then run the bar against that main rather than the obsolete b788 baseline.

## Item 0 per-law evidence

The private v4 replay proved all **20 per-input decision laws** with the existing checked prover. Published 0.47.0 and source baseline b788 refused the corresponding functions. Selecting one entry in a file containing other stated laws correctly leaves those other laws unread and exits 2; this is not a proof failure. The whole-file replay (omit `--entry`) passed with exit 0 for both files (13 + 7 laws), in `/tmp/gdp-ci-private-v5-results/whole-file-laws.log`, batch `20261110-013105-8mw8rm`; its adjacent synthetic standalone CLI regression also passed. No source text or law expressions are reproduced here.

| Law | Construct | Published 0.47 | Source baseline | Current proof verdict |
| --- | --- | --- | --- | --- |
| CLI-A01 | Finite string input; flat boolean result record | refused | refused | proven |
| CLI-A02 | Finite string input; flat boolean result record | refused | refused | proven |
| CLI-A03 | Finite string input; flat boolean result record | refused | refused | proven |
| CLI-A04 | Boolean/string record input; early returns; nullable choice result | refused | refused | proven |
| CLI-A05 | Boolean/string record input; early returns; nullable choice result | refused | refused | proven |
| CLI-A06 | Boolean/string record input; early returns; nullable choice result | refused | refused | proven |
| CLI-A07 | Boolean/string record input; early returns; nullable choice result | refused | refused | proven |
| CLI-A08 | Boolean/string record input; early returns; nullable choice result | refused | refused | proven |
| CLI-A09 | Boolean/string record input; early returns; nullable choice result | refused | refused | proven |
| CLI-A10 | Boolean/string record input; equality of choice comparisons | refused | refused | proven |
| CLI-A11 | Boolean/string record input; equality of choice comparisons | refused | refused | proven |
| CLI-A12 | Boolean/string record input; equality of choice comparisons | refused | refused | proven |
| CLI-A13 | Boolean/string record input; equality of choice comparisons | refused | refused | proven |
| MCP-B01 | Destructured finite record; early-return choice guards | refused | refused | proven |
| MCP-B02 | Destructured finite record; early-return choice guards | refused | refused | proven |
| MCP-B03 | Destructured finite record; early-return choice guards | refused | refused | proven |
| MCP-B04 | Destructured finite record; early-return choice guards | refused | refused | proven |
| MCP-B05 | Destructured finite record; early-return choice guards | refused | refused | proven |
| MCP-B06 | Not per-input: a protocol transition depends on stored destination and prior registration/authorization across calls | model retained | model retained | model retained |
| MCP-B07 | Destructured finite record; early-return choice guards | refused | refused | proven |
| MCP-B08 | Destructured finite record; early-return choice guards | refused | refused | proven |

The separate CLI-P01 flow law also remains a model law; decision proofs do not establish protocol order.

## Focused green evidence

`runs/probe-v4` / batch `20261110-010526-s9tq8y`: **61 tests passed, 0 failed** across seven focused files; `bun run check` passed with 0 warnings/errors and the build passed. This is a clean-baseline-plus-frozen-patch validation, not the required final committed-candidate gate. The new whole-file CLI regression is in the next snapshot.

## Item 3 choice and measured costs

Selected **interpreter-by-default for `Fun.run()`**, with a cached `Fun.compiled()` callable as explicit opt-in. Selection was made after the actual-example job completed successfully. `runs/item3-measurements.json` contains the numeric rows and placement from batch `20261110-010532-cfxnro` (exclusive large, AMD Ryzen 9 9950X, 2/8 vCPUs, zero co-tenants). Each row is 100,000 warm calls or 1,000 model-create/first calls; normalization was checked on every input before timing.

| Domain | Plain ns/call | Compiled ns/call | Interpreted ns/call | Cold compiled ns | Cold interpreted ns |
| --- | ---: | ---: | ---: | ---: | ---: |
| 4 | 21.10 | 2280.46 | 1708.42 | 63551.85 | 26337.34 |
| 128 | 37.03 | 3283.02 | 2856.71 | 100095.66 | 56409.08 |
| 32 | 31.44 | 3095.88 | 1818.03 | 50930.20 | 36937.96 |
| 48 (additional decision) | 16.21 | 2947.92 | 2138.37 | 53823.79 | 27948.51 |

These are wrapper-level measurements including encoding/decoding and adapters, not isolated evaluator costs or a universal speed claim. On the requested examples the interpreter was not slower, and avoided cold code generation; plain shipped TypeScript remains much cheaper. Internal prover compilation remains unchanged. `compare()` deliberately keeps a compiled execution path for tooling. Native arithmetic terms avoid helper compilation; declared helper source is refused by default before machine construction and requires the explicit opt-in (callbacks are serialized by the existing machinery too). The v6 CSP/compatibility/export probe passed **62 tests, 0 failed**. Its typecheck failed only because a test expected string was widened rather than kept as a literal; that fixture was fixed and v7 passed check, lint, build and 28 built-export/runtime tests. No final gate is claimed.

New `Fun.compiled()` API:

```ts
import {bool, fun} from 'gdp-wired'
const f = fun('permit').inputs({ready: bool}).returns(({ready}) => ({ok: ready}))
const run = f.compiled() // explicit dynamic-code opt-in; cached callable
console.log(run({ready: true}))
console.log(f.run({ready: false})) // interpreted default
```

## Coverage-preservation correction

Review of the runtime commit diff caught that the new CSP test file had replaced the pre-existing `core/runtime.test.ts` fuzz regressions. The original file was restored byte-for-byte from the baseline, and the new tests moved to `core/runtime-default.test.ts`; the quick-suite entry now names only that new file. No existing runtime coverage is intentionally removed. This is a separate corrective commit, not a history rewrite.

## Coordinator follow-up: automatic candidates and independent review

At the coordinator's request, the item-2 stretch goal is now implemented and under focused validation: `deriveDecisionMutants(machine, {file, render, choices?, maxCandidates?})` derives guard negations, dropped conjuncts, widened encoded choices and flipped comparisons. A trusted explicit printer maps the original and mutated scalar terms to the source artifact under test; it does not pretend to reverse arbitrary handwritten source. The normal mutation API performs preflight/baseline/restoration and runs individually named law suites for kill attribution. Original laws, assumptions, preconditions and initial state remain unchanged. Boat batch `20261110-014547-jg31oj` passed 33 mutation/export tests, including cap/determinism/refusal cases and the synthetic per-law end-to-end checks; check, lint, build and 28 built-export/runtime tests also passed. Every generated candidate was killed by the aggregate law suite and at least one individually named law. The follow-up captured all 11 generated candidates and their individual law kills (from `runs/probe-v9/review-repros-and-regressions.log`):

| Mutant | Bug | all-laws | ready | reviewed | zone | load | admit-valid |
| --- | --- | --- | --- | --- | --- | --- | --- |
| negate-guard-001 | negate-guard at step.state.out.ok.c | caught | caught | caught | caught | caught | caught |
| drop-conjunct-002 | drop-conjunct at step.state.out.ok.c | caught | caught | missed | missed | missed | missed |
| drop-conjunct-003 | drop-conjunct at step.state.out.ok.c | caught | missed | caught | missed | missed | missed |
| drop-conjunct-004 | drop-conjunct at step.state.out.ok.c | caught | missed | missed | caught | missed | missed |
| drop-conjunct-005 | drop-conjunct at step.state.out.ok.c | caught | missed | missed | missed | caught | missed |
| flip-comparison-006 | flip-comparison at step.state.out.ok.c.xs.0 | caught | caught | missed | missed | missed | caught |
| flip-comparison-007 | flip-comparison at step.state.out.ok.c.xs.1 | caught | missed | caught | missed | missed | caught |
| flip-comparison-008 | flip-comparison at step.state.out.ok.c.xs.2 | caught | missed | missed | caught | missed | caught |
| widen-choice-009 | widen-choice at step.state.out.ok.c.xs.2 | caught | missed | missed | caught | missed | missed |
| widen-choice-010 | widen-choice at step.state.out.ok.c.xs.2 | caught | missed | missed | caught | missed | missed |
| flip-comparison-011 | flip-comparison at step.state.out.ok.c.xs.3 | caught | missed | missed | missed | caught | missed |

New automatic-candidate API (five-line example):

```ts
import {bool, fun} from 'gdp-wired'
import {deriveDecisionMutants} from 'gdp-wired/mutate'
const f = fun('permit').inputs({ready: bool}).returns(({ready}) => ({ok: ready}))
const edits = deriveDecisionMutants(f.rule.machine, {file: 'decision.ts', render: m => `export default ${JSON.stringify(m)}\n`})
console.log(edits) // use these as checkMutations({mutants: edits, ...})
```

The one independent read-only review is running with exact model `openai/gpt-6.1-terra` (agent `60bbeb8fce8246efb2c7a9e11af5a3ff`), pinned to `b788e195..a7aaa1b2`. It covers extractor source soundness, finite comparison claims, mutation safety and default dynamic-code paths. The completed review found strict absence narrowing, literal replacement-template handling, timed-out suite descendants, and `Rule.interpreter()` helper compilation issues, plus a cross-domain choice-join hypothesis and a fixed-parameter coverage concern. Fixes are under Boat validation: preserve null tags and distinguish strict/loose comparisons; reject incompatible ordered choice joins; use literal replacements; supervise each POSIX suite group and stop exact remaining PIDs before restoring; refuse helper compilation by default with explicit `{compileHelpers: true}` available; require finite parameter kinds for an exhaustive function-comparison flag and expose fixed tuples in `parameterScope`. A regression run intentionally reverts the extractor fixes first to reproduce the original failures, then tests the repaired code. No kernel change.

The v9 negative run reproduced the old false proof (`result == false` was incorrectly proven) and accepted incompatible choice join, with replay disabled. After the fixes, the false proof is rejected and the choice join is refused. The v9 repaired run passed 70 tests but two newly written fixtures assumed unsupported nullable inputs/mutable statements; those fixtures were corrected to supported nullable locals and a conditional join. Descendant cleanup, literal edits, CSP, and all 11 automatic mutant cases passed. Check/lint/build and built exports passed; the fresh v10 combined run passed **84 tests, 0 failed**, plus check/lint/build and **29 built-export/runtime tests** (batch `20261110-015219-6f45js`). The negative old-code run still reproduced both source-soundness defects. The complete independent review is incorporated; no review agent remains active.

Explicit rule-helper interpretation (five-line example):

```ts
import {fn, rule} from 'gdp-wired'
const r = rule('increment').fns({inc: fn(1, 'x => x + 1')}).state({n: 0}).step(({n, inc}) => ({n: inc(n)}))
const runtime = r.interpreter({compileHelpers: true}) // explicit dynamic-code permission
const initial = runtime.init({})
console.log(runtime.step({}, initial, {}).scalars.n)
```

The clean committed pre-integration test run (`a7aaa1b2`, batch `20261110-014415-u5ulmj`) is still active. Its separate original runtime-guards/history suite passed. The seven full quick-suite shards are not yet claimed. This is submission-class validation, not the final post-integration gate.

## Soundness

### Exact false-proof construct

The independent review found this **synthetic** counterexample:

```ts
export function decide(flag: boolean | undefined): boolean {
  if (flag !== null) return flag === undefined;
  return false;
}
```

At input **`flag = undefined`**, JavaScript returns **true**. Before the fix, the symbolic reader treated the strict test against `null` as a presence test for an optional value whose absence was actually `undefined`, replaced `flag` with its present Boolean payload, and modeled the result as false. Consequently `result == false` could be reported **proven and kernel-checked for the wrong extracted model**. The v9/v10 negative regressions reproduced that false proof with `{check: {runs: 0, states: 0, probes: false}}`. Those options leave no concrete replay observations or branch-probe witness checks to catch the extraction error. This is not a kernel proof-checking failure.

The fix distinguishes strict and loose absence tests, preserves the null tag, and leaves the optional value intact when a strict test names the wrong absence kind. Additional conditional-join tests reject different ordered choice encodings rather than silently mixing them. The fixed regression rejects the false law, without relying on source replay.

### Clean-source origin results so far

The exact standalone absence and choice-join programs are refused by clean `b788e195` as unsupported syntax. Pre-fix `a7aaa1b2` accepts both and disagrees with their concrete results when replay is disabled; normal replay catches both and refuses extraction. Fixed `ed5af69b` produces the correct absence result with replay either on or off, and refuses the incompatible choice join. The baseline has no mutation runner, so both mutation defects are branch-introduced. Its existing `Rule.interpreter()` does try to compile helper source; the safer default is therefore a change to pre-existing behavior. Its existing `Fun.compare()` returns a sample count but no exhaustive claim; the false fixed-parameter exhaustive flag is branch-introduced.

Three completed source receipts were retained in `runs/origin/`. The remaining quick checks initially waited in the experiment queue; only the unstarted jobs were closed and moved to the documented interactive quick-check class. They completed successfully, establishing the released legacy-map case below. No running gate was stopped or duplicated.

### Confirmed released-version reachability

The actual **0.47.0 registry tarball** (SHA-256 **`ca81b4f6c641a9cc4b2c5eb3932e5ea36840c02c00bbd8ff493aedcdfb40dd6c`**) and clean `b788e195` reproduce the same false proof through the older optional-map reader:

```ts
export class Decision {
  flags = new Map<string, boolean>();
  decide(key: string): boolean {
    const flag = this.flags.get(key);
    if (flag !== null) return flag === undefined;
    return false;
  }
}
```

With the initially empty map, JavaScript returns **true** for any key. With `{check: {runs: 0, states: 0, probes: false}}`, both the released tarball and baseline accept extraction and report **`result == false` proven and checked**. Their default replay catches the discrepancy on the **first request** and refuses extraction. Fixed `ed5af69b` rejects the false law even with replay disabled and passes default checking (2,400 requests and 400 drawn-state checks). This establishes a **pre-existing released extractor soundness issue**, not merely a new standalone-reader regression. Disclosure remains held for the user; no external action was taken.

| Fix | Clean b788e195 / actual 0.47.0 | Origin |
|---|---|---|
| Strict absence narrowing | Legacy map repro produces a checked false proof with replay off; default replay refuses | Pre-existing and released; newly exposed by standalone extension too |
| Incompatible choice joins | Exact standalone repro refused as unsupported on both; accepted incorrectly by pre-fix a7 | Branch-introduced accepted-program defect for this repro |
| Literal `$&` mutation replacement | Mutation runner absent on both | Branch-introduced |
| Descendant cleanup before restoration | Mutation runner absent on both | Branch-introduced |
| Implicit compilation in `Rule.interpreter()` | Both attempt dynamic compilation of user JS source | Pre-existing behavior; explicit-source opt-in is a breaking API change |
| Exhaustive flag despite fixed parameters | Both return sampled `checked` count with no exhaustive claim | Branch-introduced claim on an existing API |

Receipts: `runs/origin/` and `runs/origin-quick/`. The unsupported old standalone join repro is not evidence that every other legacy join form is correct.

### Release-origin audit receipts (complete for ed5af69b)

All **64 published stable tarballs** were integrity-checked and tested on Boat. The first affected release is **0.26.0**, published **2026-10-24T06:56:21.399Z**, SHA-256 `da4bccbe9817fd1dc626ed1e4f95323ee0a0717d1d634ea0de0510a1aaa7f9ca`. Every stable release **0.26.0 through 0.47.0** reproduces the false proof (26 versions). Of earlier versions, 36 lack the frontend and 0.24.0/0.25.0 explicitly refuse the null expression. There were **zero unclassified results**, so this first-version finding does not depend on monotonicity. Prereleases were excluded. The exact `buildLaw` and bundled CLI arrived in 0.32.0; earlier affected versions used an equivalent direct step law, cross-checked with the convenience API on later versions.

Actual 0.32.0 and 0.47.0 bundled CLIs confirmed the user-facing switch: put `[check]` with `runs = 0`, `states = 0`, `probes = false` in `gdp.toml`. Default checking exits 2 on the mismatch; the zero-budget configuration exits 0 and reports the false law proven. These are configuration settings, not a separately established flag. Full private receipts: `/tmp/gdp-ci-release-range-confirm/{receipt.md,results/release-confirm.log}`. A short held advisory is at `/Users/monotykamary/VCS/working-remote/open-source/gdp-wired/private/handoff/advisory-extractor-null-20261110.md`, verified ignored by the main repository. Its proposed patch-release changelog remains private. No publication or external contact was made.

### Replay defaults

For the TypeScript `extract` path used here, concrete source/model checking is on by default (`core/extract.ts` calls the checker with `opts.check` merged into its defaults). Current defaults are **200 runs × 12 requests**, **400 drawn-state steps**, plus branch/witness probes unless disabled (`core/extract-check.ts`). The CLI passes source-reader options/configuration through and normally uses these defaults. This checking is sampled/probe-based evidence, not a formal correctness proof of the extractor. API users can suppress those observations with `{check: {runs: 0, states: 0, probes: false}}`; configuration forwarded by the CLI can likewise change the budgets. There is no universal guarantee that every `extract*` API uses this exact contract: XState checks its actor, and other language frontends use their own replay harnesses and budgets. In particular, Solidity re-entrancy checking retains a minimum of four attempts even when its requested run count is zero (`core/extract-sol.ts:742`); do not treat the TypeScript zero-budget recipe as a universal replay-off flag. Counterexample replay for a broken law is also a separate operation from the initial source-conformance check.

### Private plain-file proof replay — PASS

On clean `ed5af69b`, **all 20 per-input laws passed** with normal replay enabled (13 + 7, both CLI exits 0). Four actual plain decisions matched their extracted models on **all 212 finite input tuples** (4 + 128 + 32 + 48). Each decision received 2,400 start-state requests and 400 drawn-state checks; the branch-bearing decisions also received 6 and 4 witness probes. **All 24 instrumented branch arms were hit** (0 + 12 + 3 + 9). The sanitized receipt is outside the repository at `/tmp/gdp-ci-replay-final-results/plain-laws-replay-on.log`; no private source or customer names were copied into this report.


## Final-suite fixture follow-up

The corrected final wrapper actually ran the tests. Shard 2 found one missed API migration in `core/lemmas.test.ts:37`: the existing recurrence comparison deliberately uses declared helpers, so it must now request `interpreter({compileHelpers: true})`. Commit **`f62eeb59940381d9786d0dfea75178414447a5ad`** changes that test line only; all production, gate, example, and corpus files are byte-identical to `ed5af69b`. The failed shard and check/build/exports/commitlint are being rerun from a clean `f62eeb59` checkout. Already-passing shards and the ongoing `ed5af69b` bar/census are retained with their exact revision labels, not silently relabelled. The bar's `onecpu` workload uses `data.test.ts`/`infer.test.ts`; however, the full suite does include the lemmas workload. The coordinator correctly requires built-in recurrences to remain directly interpretable: the test-only workaround will be superseded by a source-free built-in helper implementation, and affected final gates must be rerun on that production change.

## Helper interpretation and the breaking API boundary

Data-built helpers now carry a serializable direct implementation: library `divBy`/`modBy`, automatically generated arithmetic, list-fold proof constants, and `recur` equations (including multiple arguments and nested source-free dependencies). These are interpreted **without `Function`, including during construction and materialization**, and need no opt-in. Their generated JavaScript remains available for explicitly compiled execution.

Only user-supplied JavaScript requires compilation permission: `fn` strings, callbacks serialized as source, and recurrence dependencies that transitively contain either. `rule.interpreter()` refuses these with **`use compiled() or explicitly pass {compileHelpers: true}`**; `fun.run()` names **`use compiled() explicitly`**. Compilation permission is not implied by having called the compiled path previously. User callbacks are not executed for constant folding before that permission. This is a breaking change for source-helper callers and is labelled **Breaking** in `CHANGELOG.md`.

Migration inventory:

| Test/example | Final requirement |
|---|---|
| `core/runtime-default.test.ts` — explicit custom-source and transitive-source tests | Uses `{compileHelpers: true}` or `compiled()` deliberately; tests the refusal text as well |
| `core/lemmas.test.ts` — recurrence comparison | No opt-in; the temporary f62 workaround is removed |
| `core/functions.test.ts` — library `modBy` decision | No opt-in; checks default and compiled parity |
| `examples/jev-fabric/laws.ts` — library `modBy` cap witness | No opt-in; restored to `.run()` |

No pre-existing example requires a new source-helper opt-in after this correction. Existing explicit compiled-engine tests/examples remain explicit by choice, not because data-built helpers require compilation. Focused Boat validation before final freezing passed **47 tests / 3,941 expectations**, check (typecheck + lint), and build. CSP coverage blocks `Function` before import, construction, materialization and execution, and covers serialized machines, multiargument/nested recurrences, proved recurrences, list helpers and direct/transitive custom-source rejection. Independent review found no ordinary-input arithmetic, memoization or argument-pairing mismatch. It did identify stale public helper metadata after a JavaScript/arity override, plus generated-code identifier shadowing; a focused consistency follow-up addresses source/arity/descriptor changes, warm caches, actual transitive dependencies, and invalid generated-code parameter names. Direct metadata remains a trusted representation, not provenance for manually forged objects. The final focused follow-up passed **55 tests / 4,082 assertions**, check and build (`/tmp/gdp-builtins-run-v7/`). A final compatibility regression preserves `Map` as a safe recurrence argument; the clean final gate includes it. Final quick-gate validation remains pending.

## Earlier full-gate attempt (superseded)

The coordinator reported that the unrelated integration gate is red and explicitly requested final validation now against `b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`, using candidate `ed5af69b`. Planned work: clean Boat check/build/full quick suite, both 29-protocol generation censuses, and the full Boat bar. A known `core/effect-queue.test.ts:55` failure is being checked on both revisions and will not be silently counted as green. The full bar may produce more than 500 MB of raw logs; summaries and hashes are the retained evidence, bulky raw logs may be compressed/offloaded, and no duplicate tree archives will be made. No final gate is claimed yet.

The initial final-test wrapper used the shard label `1/7` inside a log filename, so all seven test jobs failed before running tests (missing log subdirectory). This is an owned harness error, not a code failure. The wrapper was corrected and only those seven jobs resubmitted; successful check/build/exports/commitlint and census work are retained. The completed census compared all 29 IDs: **28 proven and `mldr` unknown on both sides; every verdict unchanged** (`runs/census-final.json`). The standalone baseline effect-queue test passed in this run; any later failure will still be checked against its baseline evidence. The earlier clean a7 pre-integration run finished all seven shards plus the original runtime fuzz suite successfully (8 jobs, 0 failed), but is not substituted for the final candidate gate.

## Scheduling change — quick submission gate

At the coordinator's explicit priority change, the full gate-class bar was stopped by exact PID **33220**. Its partial receipts remain in `runs/bar/runs/final-ed5af69b`; they are not a completed green gate. The merge standard is now **`--quick --together --cand <final head> --base b788e195 --runs 3`** with **`SUPERCOMPUTER_CLASS=submission`**, plus check, tests, and the census. The census will also run as submission work to share capacity with the primary MLDR lanes. Inspection found that `gates/bar.ts` previously overwrote the explicit scheduler class (globally and in g332); the launcher now honors `SUPERCOMPUTER_CLASS`, with a submission-class CLI regression in the final checks.

## Remaining validation

The source-free built-in helper follow-up is under independent review. Freeze and commit that candidate, then run the affected clean-checkout tests/build, the **quick, together, submission-class Boat bar** against unchanged `b788e195`, and the final submission-class census. Do not substitute the earlier `ed5af69b`/`f62eeb59` receipts for a production change. The coordinator explicitly said main will not move soon; no rebase wait is required. An exhaustive comparison is a test, never a proof. No kernel proof logic or protected MLDR file was changed.
