// The quick suite (`bun run test`) as a list of units, and one CI job's share of it.
//   bun scripts/test-shards.ts                       every unit, in order: what `bun run test` runs
//   bun scripts/test-shards.ts --shard 2/7           shard 2 of 7
//   bun scripts/test-shards.ts --list [--shard i/N]  the units (each shard's, with its estimate, given --shard i/N or N)
//   bun scripts/test-shards.ts --measure out.json [--shard i/N]   each unit alone, its seconds written to out.json
// A unit is a test file bun test runs in its directory, or a script bun runs from the root. Consecutive test files of one
// directory run in one `bun test`, as the && chain did, and the first failure stops the run with its code. The shards
// are balanced on test-shards.json's seconds (measured on boat, each unit alone: --measure), longest first onto the
// least loaded shard; a unit not measured yet goes round-robin. Every unit is in exactly one shard (checked each run).
import {spawnSync} from 'node:child_process'
import {readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'

type Unit = {name: string, dir: string, args: string[], test: boolean}
const root = join(import.meta.dir, '..')
const tests = (dir: string, files: string) => files.split(/\s+/).filter(Boolean).map((f): Unit =>
  ({name: dir === '.' ? f : `${dir}/${f}`, dir, args: [f], test: true}))
const runs = (cmds: string) => cmds.split(/\s+/).filter(Boolean).map((f): Unit => ({name: f, dir: '.', args: [f], test: false}))

const units: Unit[] = [
  {name: 'scripts/gen-lean-library.ts --check', dir: '.', args: ['scripts/gen-lean-library.ts', '--check'], test: false},
  ...tests('core', `exports.test.ts guarded.test.ts cli.test.ts security.test.ts solver.test.ts rand.test.ts dsl.test.ts sums.test.ts
    arith.test.ts conformance.test.ts compose.test.ts relational.test.ts quantifiers.test.ts functions.test.ts
    keyterms.test.ts lists.test.ts liveness.test.ts sizes.test.ts values.test.ts rationals.test.ts builders.test.ts
    gdp.test.ts datatypes.test.ts lemmas.test.ts discover.test.ts infer.test.ts cyclic.test.ts cycles.test.ts
    nonterm.test.ts data.test.ts data-synth.test.ts hypothesis.test.ts seqs.test.ts abstract.test.ts search.test.ts invoices.test.ts
    folds.test.ts trees.test.ts pairs.test.ts chart.test.ts xstate.test.ts extract.test.ts extract-standalone.test.ts extract-standalone-prototype.test.ts extract-standalone-regression.test.ts extract-py.test.ts extract-py-mro.test.ts extract-py-hasattr.test.ts extract-orm.test.ts extract-py-orm.test.ts sol-concrete.test.ts effect.test.ts
    effect-schedule.test.ts effect-stm.test.ts effect-queue.test.ts effect-schema.test.ts calendar.test.ts count-facts.test.ts count-witness.test.ts count-unions.test.ts count-witness-flags.test.ts count-focused.test.ts count-cases.test.ts count-focus-proof.test.ts count-recovery-order.test.ts count-cert-grow.test.ts field-laws.test.ts bitsets.test.ts sample-cache.test.ts small-laws.test.ts cube-width.test.ts exists-support.test.ts carry.test.ts scan-prefix.test.ts
    count-support.test.ts count-admission.test.ts counts-preflight.test.ts counts-structured.test.ts relevance.test.ts support-order.test.ts`),
  ...tests('core/count-recovery', 'action-guard.test.ts row-cases.test.ts natural-cases.test.ts carried-case.test.ts live-dependencies.test.ts field-bound-lemmas.test.ts boolean-core.test.ts key-closure.test.ts lift-count-proxies.test.ts rebase-path.test.ts fold-path.test.ts frame-lemmas.test.ts guard-cases.test.ts field-only.test.ts source-memo.test.ts'),
  ...tests('kernel', 'tamper.test.ts refusals.test.ts steplaw.test.ts sets.test.ts cdcl.test.ts tuples.test.ts epr-clock.test.ts epr-image.test.ts triggers.test.ts share.test.ts model-sequence.test.ts model-values.test.ts prove-paths.test.ts'),
  ...tests('research/query', 'goal-pack.test.ts'),
  ...tests('research/protocols/ic3syn', 'mldr.test.ts'),
  ...tests('research/audit', 'inventory.test.ts'),
  ...tests('examples', 'examples.test.ts'),
  ...tests('gates', 'bar.test.ts'),
  ...tests('.', 'scripts/action.test.ts scripts/lean-gate/gate.test.ts'),
  ...runs(`examples/readme.ts examples/guide.ts examples/composition.ts examples/sets.ts examples/quantifiers.ts
    examples/functions.ts examples/datatypes.ts examples/lemmas.ts examples/discover.ts examples/invoices.ts
    examples/folds.ts examples/trees.ts examples/pairs.ts examples/groups.ts examples/charts.ts examples/xstate.ts
    examples/effect.ts examples/effect-retry.ts examples/effect-stm.ts examples/effect-queue.ts examples/infer.ts
    examples/arith.ts examples/cyclic.ts examples/cycles.ts examples/data.ts examples/abstract.ts`),
  ...tests('.', 'compare/tip/translate.test.ts research/security/score.test.ts research/security/fixed-reader.test.ts research/security/mutants/mutants.test.ts research/security/mutants-upstream/upstream.test.ts'),
  ...runs(`examples/scopes.ts examples/lists.ts examples/sizes.ts examples/liveness.ts examples/sums.ts
    examples/nonterm.ts examples/rationals.ts examples/budget.ts examples/gdp.ts examples/steps.ts
    examples/jev-fabric/run.ts`),
  ...tests('gates', 'bar-lib.test.ts'),
]

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

const run = (dir: string, args: string[]) => {
  console.error(`$ ${dir === '.' ? '' : `(cd ${dir}) `}bun ${args.join(' ')}`)
  const t0 = performance.now()
  const r = spawnSync('bun', args, {cwd: join(root, dir), stdio: 'inherit'})
  return {code: r.status ?? 1, s: (performance.now() - t0) / 1000}
}

const out = flag('--measure')
if (out !== undefined) {
  // Each unit alone, so its seconds are its own; every unit runs, and the run fails if any did.
  const got: Record<string, number> = {}
  let failed = 0
  for (const u of mine) {
    const {code, s} = run(u.dir, u.test ? ['test', ...u.args] : u.args)
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
  if (u.test) {
    let j = k + 1
    while (j < mine.length && mine[j]!.test && mine[j]!.dir === u.dir) j++
    batch = mine.slice(k, j)
  }
  k += batch.length
  const {code, s} = run(u.dir, u.test ? ['test', ...batch.flatMap(b => b.args)] : u.args)
  took.push(`${s.toFixed(1).padStart(7)} s  ${batch.map(b => b.name).join(' ')}`)
  if (code !== 0) { console.error(took.join('\n')); process.exit(code) }
}
console.error(took.join('\n'))
