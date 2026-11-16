// The quick suite (`bun run test`) as a list of units, and one CI job's share of it.
//   bun scripts/test-shards.ts                       every unit, in order: what `bun run test` runs
//   bun scripts/test-shards.ts --shard 2/7           shard 2 of 7
//   bun scripts/test-shards.ts --list [--shard i/N]  the units (each shard's, with its estimate, given --shard i/N or N)
//   bun scripts/test-shards.ts --measure out.json [--shard i/N]   each unit alone, its seconds written to out.json
// A unit is a test file or script, with explicit per-file process configuration where required. Consecutive compatible
// test files share one `bun test`; isolated/profile-specific units never share its module cache. The shards
// are balanced on test-shards.json's seconds (measured on boat, each unit alone: --measure), longest first onto the
// least loaded shard; a unit not measured yet goes round-robin. Every unit is in exactly one shard (checked each run).
import {spawnSync} from 'node:child_process'
import {readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {assertTestRoster, coreKernelTests, longSuiteTests} from './test-roster.ts'

type UnitConfig = {rootCwd?: boolean, isolated?: boolean, env?: Record<string, string | undefined>, timeoutMs?: number}
type Unit = {name: string, dir: string, args: string[], test: boolean} & UnitConfig
const root = join(import.meta.dir, '..')
const tests = (dir: string, files: string) => files.split(/\s+/).filter(Boolean).map((f): Unit =>
  ({name: dir === '.' ? f : `${dir}/${f}`, dir, args: [f], test: true}))
const runs = (cmds: string) => cmds.split(/\s+/).filter(Boolean).map((f): Unit => ({name: f, dir: '.', args: [f], test: false}))

const units: Unit[] = [
  {name: 'scripts/gen-lean-library.ts --check', dir: '.', args: ['scripts/gen-lean-library.ts', '--check'], test: false},
  ...tests('core', `exports.test.ts proof-output.test.ts protocol-refusal.test.ts deterministic-work.test.ts public-budget-ownership.test.ts search-watchdog.test.ts effect-budget.test.ts infer-termination.test.ts infer-completion-boundary.test.ts guarded.test.ts cli.test.ts cli-deadline.test.ts cli-two-run-budget.test.ts lift-cli.test.ts security.test.ts solver.test.ts rand.test.ts dsl.test.ts dsl-binders.test.ts dsl-binder-groups.test.ts prenex-admission.test.ts generated-provenance.test.ts sums.test.ts
    arith.test.ts compare.test.ts mutate.test.ts mutate-terms.test.ts runtime-default.test.ts conformance.test.ts compose.test.ts relational.test.ts quantifiers.test.ts functions.test.ts
    keyterms.test.ts lists.test.ts liveness.test.ts sizes.test.ts values.test.ts rationals.test.ts builders.test.ts
    gdp.test.ts datatypes.test.ts lemmas.test.ts discover.test.ts discover-budget.test.ts infer.test.ts infer-input.test.ts cyclic.test.ts cycles.test.ts
    nonterm.test.ts data.test.ts data-synth.test.ts hypothesis.test.ts seqs.test.ts abstract.test.ts search.test.ts invoices.test.ts
    folds.test.ts trees.test.ts pairs.test.ts chart.test.ts chart-provenance.test.ts xstate.test.ts extract.test.ts extract-standalone.test.ts extract-ci-method-scope.test.ts source-check.test.ts source-completion.test.ts source-diagnostic.test.ts extract-absence.test.ts extract-choice-joins.test.ts extract-standalone-prototype.test.ts extract-standalone-regression.test.ts extract-py.test.ts extract-step-native.test.ts extract-py-mro.test.ts extract-py-hasattr.test.ts extract-orm.test.ts extract-py-orm.test.ts extract-sol.test.ts sol-concrete.test.ts effect.test.ts
    effect-schedule.test.ts effect-stm.test.ts effect-queue.test.ts effect-schema.test.ts calendar.test.ts count-facts.test.ts count-ranges.test.ts count-write-frames.test.ts counts-completion-order.test.ts count-completion.test.ts count-witness.test.ts count-unions.test.ts count-witness-flags.test.ts count-focused.test.ts count-cases.test.ts count-focus-proof.test.ts count-recovery-order.test.ts count-cert-grow.test.ts field-laws.test.ts count-cubes.test.ts finite-tiny.test.ts finite-tiny-houdini.test.ts bitsets.test.ts sample-cache.test.ts small-laws.test.ts cube-width.test.ts exists-support.test.ts carry.test.ts scan-prefix.test.ts
    runtime-keys.test.ts sample-step.test.ts small-counts.test.ts cube-rows.test.ts quorum-laws.test.ts wall.test.ts count-demand.test.ts count-cert-transport.test.ts count-tier-budget.test.ts work-admission-perf.test.ts i6-meter.test.ts prover-row-budget.test.ts count-attempt-expiration.test.ts common-counted.test.ts hard-cap.test.ts work-observe.test.ts
    lemma-cuts.test.ts count-support.test.ts count-admission.test.ts counts-preflight.test.ts counts-structured.test.ts relevance.test.ts support-order.test.ts`),
  // Explicit quick coverage for tests absent from the legacy roster.
  ...tests('core', `
    count-attempt-tickets.test.ts count-boolean-partition.test.ts count-case-compose.test.ts
    count-cert-rename.test.ts count-cert-transport-hard-stop.test.ts count-certificate-minimize.test.ts
    count-closed-family.test.ts count-closing-budget.test.ts count-closing-envelope.test.ts
    count-closing-needs.test.ts count-closing-retry.test.ts count-component-budget.test.ts
    count-cut-transport.test.ts count-deferred-checks.test.ts count-disjoint-funding.test.ts
    count-emitter-frame-pool.test.ts count-final-step.test.ts count-frames.test.ts
    count-g1-lease.test.ts count-generation-parent-cap.test.ts count-generation-phase.test.ts
    count-guard-shape.test.ts count-guard-tree.test.ts count-leader-facts.test.ts
    count-lemma-transport.test.ts count-lifted-budget-profile.test.ts count-lifted-budget.test.ts
    count-lifted-emitter-boundary.test.ts count-lifted-helper-budget.test.ts count-lifted-increment.test.ts
    count-lifted-lease.test.ts count-lifted-shape.test.ts count-lifted-transports.test.ts
    count-minimal-view.test.ts count-operation-order.test.ts count-owner-budget.test.ts
    count-phase.test.ts count-premise-integration.test.ts count-premise-search.test.ts
    count-premise-view.test.ts count-prerequisite-components.test.ts count-prerequisite-discovery.test.ts
    count-prerequisite-expiration.test.ts count-prerequisite-memory.test.ts count-prerequisite-plan.test.ts
    count-prerequisite-public.test.ts count-prerequisite-scope-expiry.test.ts count-prerequisite-unknown.test.ts
    count-primitive-budget.test.ts count-proof-guided-scheduler.test.ts count-proof-rescope-identity.test.ts
    count-proof-rescope.test.ts count-proof-scope.test.ts count-prune-owned-root.test.ts
    count-query.test.ts count-quorum-leaf.test.ts count-reachability-gate.test.ts
    count-reachability-queue.test.ts count-reachability-reconcile.test.ts count-reachability.test.ts
    count-recipe-allocation.test.ts count-recipe-candidates.test.ts count-recipe-cohort.test.ts
    count-recipe-context-public.test.ts count-recipe-context.test.ts count-recipe-controller.test.ts
    count-recipe-diagnostics.test.ts count-recipe-graph.test.ts count-recipe-prover.test.ts
    count-recovery/reframe-tree.test.ts count-reindex-budget.test.ts count-rejection-budget.test.ts
    count-replay-forward-lease.test.ts count-replay-forward.test.ts count-replay-skeleton.test.ts
    count-required-family.test.ts count-retry-budget.test.ts count-row-agreement.test.ts
    count-row-composition.test.ts count-row-copy-linear.test.ts count-row-reindex.test.ts
    count-row-symmetry.test.ts count-scope-hyps.test.ts count-scope-lazy.test.ts
    count-scope-row-reuse.test.ts count-search-policy.test.ts count-section46-acceptance.test.ts
    count-stage-trace.test.ts count-strategies.test.ts count-strategy-clock.test.ts
    count-strategy-kind.test.ts count-strategy-lease.test.ts count-strategy-premises.test.ts
    count-strategy.test.ts count-structured-deadline.test.ts count-tier-integration.test.ts
    count-work.test.ts dsl-budget-inheritance.test.ts dsl-deadline.test.ts
    evaluation-admission.test.ts field-loaded.test.ts finite-work.test.ts
    linear-admission.test.ts prover-row-admission.test.ts public-closing-proposal.test.ts
    reader-endpoint.test.ts rejection-discovery.test.ts rejection-stage.test.ts
    rejection-transaction.test.ts request-quotient.test.ts row-agreement-shape.test.ts
    search-policy.test.ts sized-sort.test.ts solver-deadline.test.ts strategy-premises.test.ts inherited-wall.test.ts
    table-admission.test.ts work-admission.test.ts work-amount.test.ts
    work-capacity-boundary.test.ts work-collections.test.ts work-deadline-boundary.test.ts
    work-public-exact.test.ts work-refusal.test.ts`),
  ...tests('core/count-recovery', 'conditional-check-cache.test.ts conditional-cuts.test.ts conditional-proof.test.ts derivability-closure.test.ts empty-count-source.test.ts field-bound-budget.test.ts leaf-allowance.test.ts member-inclusions.test.ts pre-state-source.test.ts rename-proof.test.ts row-demand.test.ts scalar-guards.test.ts source-witness-instances.test.ts member-premises.test.ts action-guard.test.ts row-cases.test.ts natural-cases.test.ts carried-case.test.ts live-dependencies.test.ts field-bound-lemmas.test.ts boolean-core.test.ts key-closure.test.ts lift-count-proxies.test.ts rebase-path.test.ts fold-path.test.ts frame-lemmas.test.ts guard-cases.test.ts field-only.test.ts source-memo.test.ts field-demand.test.ts'),
  ...tests('kernel', 'reader-safety.test.ts cdcl-root.test.ts frame-cut.test.ts lemma-cut.test.ts tamper.test.ts refusals.test.ts steplaw.test.ts sets.test.ts cdcl.test.ts tuples.test.ts epr-clock.test.ts epr-image.test.ts triggers.test.ts share.test.ts model-sequence.test.ts model-confirmation.test.ts model-rounds.test.ts model-values.test.ts prove-paths.test.ts prove-memo.test.ts prover-rows.test.ts prover-row-cache.test.ts tree-reuse.test.ts'),
  ...tests('lean-kernel', 'axiom-audit.test.ts lift-legacy.test.ts lift-names.test.ts frame-export.test.ts linear-export.test.ts'),
  ...tests('lean-kernel/lift', `counted-source-data.test.ts generic-lift.test.ts pipeline.test.ts prelude.test.ts
    proof-capture.test.ts proof-codec.test.ts proof-counted-source.test.ts proof-parts.test.ts
    proof-projection.test.ts proof-witness.test.ts source-projection.test.ts project.test.ts`),
  ...tests('lean-kernel/lift-special', 'bound-inclusion.test.ts'),
  ...tests('lean-kernel/lift-typed', 'roles.test.ts'),
  ...tests('lean-kernel/lift-simulation', 'shape.test.ts'),
  ...tests('research/bapa', 'lift-regression.test.ts'),
  // These controls enforce the full canonical release gate, not just this quick roster.
  ...tests('.', 'scripts/release-ci/full-gate-contract.test.ts scripts/release-ci/full-gate-runner.test.ts scripts/release-ci/full-gate-worker.test.ts scripts/release-ci/full-gate-native.test.ts scripts/release-ci/verify-publish-gate.test.ts scripts/release-ci/known-failures.test.ts'),
  ...tests('research/query', 'goal-pack.test.ts'),
  ...tests('research/translation-fuzz', 'model.test.ts'),
  ...runs('research/translation-fuzz/smoke.ts'),
  ...tests('research/protocols/ic3syn', 'mldr.test.ts'),
  ...tests('research/audit', 'inventory.test.ts'),
  ...tests('examples', 'examples.test.ts'),
  ...tests('gates', 'bar.test.ts'),
  ...tests('.', 'scripts/action.test.ts scripts/test-roster.test.ts scripts/lean-gate/gate.test.ts research/lane-i/test-load-propagation.test.ts research/lane-i/validation-audit.test.ts research/lane-i/upper-bound/summarize.test.ts research/lane-i/upper-bound/audit.test.ts research/lane-i/regressions/receipt-audit.test.ts research/lane-i/regressions/p1-scheduling-audit.test.ts research/mldr-incl/pack-production.test.ts research/track-m/link-lane-b-focus-audits.test.ts research/track-m/audit-completion-scope.test.ts research/track-wall/trace-error.test.ts core/count-recovery/row-premises.test.ts core/finite-tiny-target.test.ts core/finite-tiny-early.test.ts core/finite-tiny-seed.test.ts research/lane-i/regressions/merge-bisect-audit.test.ts research/lane-i/regressions/consensus-recheck.test.ts research/lane-i/regressions/resource-run.test.ts research/lane-i/regressions/bar-portfolio.test.ts research/mldr-incl/range-regression-input.test.ts research/mldr-incl/install-member-source-rank.test.ts'),
  ...runs(`examples/readme.ts examples/guide.ts examples/composition.ts examples/sets.ts examples/quantifiers.ts
    examples/functions.ts examples/datatypes.ts examples/lemmas.ts examples/discover.ts examples/invoices.ts
    examples/folds.ts examples/trees.ts examples/pairs.ts examples/groups.ts examples/charts.ts examples/xstate.ts
    examples/effect.ts examples/effect-retry.ts examples/effect-stm.ts examples/effect-queue.ts examples/infer.ts
    examples/arith.ts examples/cyclic.ts examples/cycles.ts examples/data.ts examples/abstract.ts`),
  ...tests('.', 'compare/tip/translate.test.ts research/security/surface-lowering.test.ts research/security/score.test.ts research/security/fixed-reader.test.ts research/security/mutants/mutants.test.ts research/security/mutants-upstream/upstream.test.ts'),
  ...runs(`examples/scopes.ts examples/lists.ts examples/sizes.ts examples/liveness.ts examples/sums.ts
    examples/nonterm.ts examples/rationals.ts examples/budget.ts examples/gdp.ts examples/steps.ts
    examples/jev-fabric/run.ts`),
  ...tests('gates', 'bar-lib.test.ts'),
]

// These files declare fresh-process/FULL or root-relative subprocess contracts.
// Keep the default process environment unchanged for every other quick unit.
const full: UnitConfig = {rootCwd: true, isolated: true, timeoutMs: 120000,
  env: {GDP_WORK_FULL: '1', GDP_WORK_STEPS: '0', GDP_WORK_WEIGHTS: undefined, GDP_WORK_W: undefined}}
const rootProcess: UnitConfig = {rootCwd: true, isolated: true}
const unitConfig: Record<string, UnitConfig> = {
  'core/count-owner-budget.test.ts': full,
  'core/count-recipe-context-public.test.ts': full,
  'core/count-recipe-cohort.test.ts': full,
  'core/count-section46-acceptance.test.ts': full,
  'core/work-capacity-boundary.test.ts': full,
  'core/count-scope-lazy.test.ts': {...full, env: {...full.env, GDP_ROWS_SHARED: '1'}},
  'core/count-strategy-lease.test.ts': full,
  'core/work-public-exact.test.ts': full,
  'core/count-prerequisite-expiration.test.ts': full,
  'core/count-replay-forward-lease.test.ts': full,
  'core/reader-endpoint.test.ts': full,
  'core/count-g1-lease.test.ts': full,
  'core/count-recipe-diagnostics.test.ts': full,
  'core/count-reindex-budget.test.ts': full,
  'core/count-structured-deadline.test.ts': full,
  'core/count-recipe-prover.test.ts': full,
  'core/count-prerequisite-public.test.ts': {...full, env: {...full.env, GDP_COUNT_STRATEGIES: '1', GDP_COUNT_TIERS: '1', GDP_COUNT_PREREQUISITES: '1', GDP_COUNT_CLOSING_RESERVE: '1', GDP_COUNT_FINAL_DEFER_CHECKS: '1'}},
  'core/count-prerequisite-scope-expiry.test.ts': {...full, env: {...full.env, GDP_COUNT_STRATEGIES: '1', GDP_COUNT_TIERS: '1', GDP_COUNT_PREREQUISITES: '1', GDP_COUNT_CLOSING_RESERVE: '1', GDP_COUNT_FINAL_DEFER_CHECKS: '1'}},
  'core/public-closing-proposal.test.ts': {...full, env: {...full.env, GDP_COUNT_STRATEGIES: '1', GDP_COUNT_TIERS: '1', GDP_COUNT_FINAL_DEFER_CHECKS: '1'}},
  'core/deterministic-work.test.ts': {...rootProcess, timeoutMs: 300000},
  'core/public-budget-ownership.test.ts': {...rootProcess, timeoutMs: 60000},
  'core/discover-budget.test.ts': {...rootProcess, timeoutMs: 60000},
  'core/search-watchdog.test.ts': {...rootProcess, timeoutMs: 60000},
  'core/source-completion.test.ts': {...rootProcess, timeoutMs: 60000},
  'core/effect-budget.test.ts': {...rootProcess, timeoutMs: 60000},
  'core/infer-termination.test.ts': {...rootProcess, timeoutMs: 300000},
  'core/infer-completion-boundary.test.ts': {...rootProcess, timeoutMs: 240000},
  'core/cli-deadline.test.ts': {...rootProcess, timeoutMs: 300000},
  'core/cli-two-run-budget.test.ts': {...rootProcess, timeoutMs: 120000},
  'core/extract-step-native.test.ts': {...rootProcess, timeoutMs: 180000},
  'core/inherited-wall.test.ts': rootProcess,
  'core/common-counted.test.ts': rootProcess,
  // Its child allows 120s; the outer Bun default 5s must not kill that child first.
  'core/i6-meter.test.ts': {...rootProcess, timeoutMs: 130000},
  'core/wall.test.ts': rootProcess,
  'core/prover-row-budget.test.ts': rootProcess,
  'core/hard-cap.test.ts': rootProcess,
  'core/work-admission-perf.test.ts': rootProcess,
  'core/work-observe.test.ts': rootProcess,
  'core/count-lifted-budget-profile.test.ts': rootProcess,
  'core/count-closed-family.test.ts': rootProcess,
  'core/count-proof-rescope.test.ts': rootProcess,
  'core/count-scope-row-reuse.test.ts': {...rootProcess, timeoutMs: 120000},
}
for (const [name, config] of Object.entries(unitConfig)) {
  const unit = units.find(u => u.name === name)
  if (!unit?.test) throw new Error(`configuration has no quick test unit: ${name}`)
  Object.assign(unit, config)
}

assertTestRoster(coreKernelTests(root), units.filter(u => u.test).map(u => u.name),
  longSuiteTests(JSON.parse(readFileSync(join(root, 'supercomputer/suite.json'), 'utf8'))))

const timingsFile = join(import.meta.dir, 'test-shards.json')
const seconds: Record<string, number> = (JSON.parse(readFileSync(timingsFile, 'utf8')) as {seconds: Record<string, number>}).seconds

function shards(n: number): Unit[][] {
  const out: Unit[][] = Array.from({length: n}, () => [])
  const load = new Array<number>(n).fill(0)
  const measured = units.filter(u => u.name in seconds).sort((a, b) => seconds[b.name]! - seconds[a.name]!)
  for (const u of measured) {
    const i = load.indexOf(Math.min(...load))
    out[i]!.push(u); load[i]! += seconds[u.name]!
  }
  units.filter(u => !(u.name in seconds)).forEach((u, k) => out[k % n]!.push(u))
  // In the suite's order within a shard, so consecutive test files of one directory still share a bun test.
  const at = new Map(units.map((u, k) => [u, k]))
  for (const s of out) s.sort((a, b) => at.get(a)! - at.get(b)!)
  // Every unit in exactly one shard, and no two units alike.
  const names = new Set(units.map(u => u.name))
  if (names.size !== units.length) throw new Error('two units have one name')
  const seen = out.flat().map(u => u.name)
  if (seen.length !== units.length || new Set(seen).size !== names.size || seen.some(s => !names.has(s)))
    throw new Error(`shards of ${n}: every unit is in exactly one shard`)
  return out
}

const estimate = (us: Unit[]) => us.reduce((t, u) => t + (seconds[u.name] ?? 0), 0)
const argv = process.argv.slice(2)
const flag = (f: string) => { const i = argv.indexOf(f); return i < 0 ? undefined : argv[i + 1] }
const shard = flag('--shard')
let mine = units
if (shard !== undefined) {
  const m = /^(\d+)\/(\d+)$/.exec(shard)
  const [i, n] = m ? [Number(m[1]), Number(m[2])] : [0, 0]
  if (!(n >= 1 && i >= 1 && i <= n)) throw new Error(`--shard i/N with 1 <= i <= N: ${JSON.stringify(shard)}`)
  mine = shards(n)[i - 1]!
}

if (argv.includes('--list')) {
  if (shard !== undefined) {
    const n = Number(shard.split('/')[1])
    shards(n).forEach((s, k) => console.log(`shard ${k + 1}/${n}: ${s.length} units, ~${Math.round(estimate(s))} s`))
  }
  for (const u of mine) console.log(`${u.name}${u.name in seconds ? `  ${seconds[u.name]} s` : '  (not measured)'}`)
  process.exit(0)
}

const run = (unit: Unit, args: string[]) => {
  const dir = unit.rootCwd ? '.' : unit.dir
  const files = unit.test && unit.rootCwd ? args.slice(1).map(file => join(unit.dir, file)) : args.slice(1)
  const command = unit.test ? ['test', ...(unit.timeoutMs ? ['--timeout', String(unit.timeoutMs)] : []), ...files] : args
  const flags = Object.entries(unit.env ?? {}).map(([key, value]) => `${key}=${value ?? '<unset>'} `).join('')
  console.error(`$ ${dir === '.' ? '' : `(cd ${dir}) `}${flags}bun ${command.join(' ')}`)
  const t0 = performance.now()
  const r = spawnSync('bun', command, {cwd: join(root, dir), env: unit.env ? {...process.env, ...unit.env} : process.env, stdio: 'inherit'})
  return {code: r.status ?? 1, s: (performance.now() - t0) / 1000}
}

const out = flag('--measure')
if (out !== undefined) {
  // Each unit alone, so its seconds are its own; every unit runs, and the run fails if any did.
  const got: Record<string, number> = {}
  let failed = 0
  for (const u of mine) {
    const {code, s} = run(u, u.test ? ['test', ...u.args] : u.args)
    got[u.name] = Math.round(s * 10) / 10
    if (code !== 0) { failed++; console.error(`FAILED (${code}): ${u.name}`) }
  }
  writeFileSync(out, `${JSON.stringify(got, null, 2)}\n`)
  process.exit(failed ? 1 : 0)
}

const took: string[] = []
for (let k = 0; k < mine.length;) {
  const u = mine[k]!
  let batch = [u]
  if (u.test && !u.isolated) {
    let j = k + 1
    while (j < mine.length && mine[j]!.test && !mine[j]!.isolated && mine[j]!.dir === u.dir && mine[j]!.rootCwd === u.rootCwd && mine[j]!.env === u.env && mine[j]!.timeoutMs === u.timeoutMs) j++
    batch = mine.slice(k, j)
  }
  k += batch.length
  const {code, s} = run(u, u.test ? ['test', ...batch.flatMap(b => b.args)] : u.args)
  took.push(`${s.toFixed(1).padStart(7)} s  ${batch.map(b => b.name).join(' ')}`)
  if (code !== 0) { console.error(took.join('\n')); process.exit(code) }
}
console.error(took.join('\n'))
