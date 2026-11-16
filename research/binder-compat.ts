// Fresh-process, byte-for-byte binder compatibility audit. No identifier rewriting.
// Run after the binder edits settle, on supercomputer: bun research/binder-compat.ts [--machine-only] [--case NAME]
// The baseline must be present on that host, or supplied via BINDER_BASELINE; see the Main handoff.
import {spawnSync} from 'node:child_process'
import {resolve} from 'node:path'
import {pathToFileURL} from 'node:url'

const cases = ['exists-ledger', 'quantified-flags', 'list', 'sequence', 'sum', 'nodes'] as const
const script = import.meta.path
const baseline = resolve(process.env.BINDER_BASELINE ?? '/tmp/lowering-old-c08bb385b')
const current = resolve(process.env.BINDER_CURRENT ?? process.cwd())
const args = process.argv.slice(2)
const child = args[0] === '--child'
const selected = args.includes('--case') ? args[args.indexOf('--case') + 1] : undefined
if (selected && !cases.includes(selected as typeof cases[number])) throw Error(`unknown case ${selected}`)

if (child) {
  const root = resolve(args[1]!), name = args[2]!, machineOnly = args[3] === 'machine'
  const load = (path: string) => import(pathToFileURL(resolve(root, path)).href)
  // Each case loads exactly the same modules, in the same order, on both sides.
  let item: any
  if (name === 'exists-ledger') {
    const x = await load('examples/exists.ts'), r = x.ledger()
    item = {id: 'ledger', machine: r.machine, laws: x.ledgerLaws(r)}
  } else if (name === 'quantified-flags') {
    const x = await load('examples/quantifiers.ts'), r = x.inlineAuthority()
    item = {id: 'inline', machine: r.machine, laws: x.inlineLaws(r), stepLaws: x.inlineSteps(r)}
  } else if (name === 'list') {
    const x = await load('examples/lists.ts'), r = x.scope()
    item = {id: 'scope', machine: r.machine, laws: x.scopeLaws(r), stepLaws: x.scopeSteps(r)}
  } else if (name === 'sequence') {
    const x = await load('core/dsl.ts')
    const r = x.rule('seqs').inputs({n: x.nat, x: x.nat}).carriesSeq('A', 'B', 'C').carriesSeqs('T')
      .state({z: 0}).step(({A, B, T, n}: any) => ({z: x.when(A.prefixOf(B), 1, 0).plus(x.when(A.equals(B), 2, 0)).plus(x.when(T.row(n).startsWith(A), 4, 0))}))
    item = {id: 'sequence', machine: r.machine, laws: [r.law('z is nonnegative', ({z}: any) => z.atLeast(0))]}
  } else if (name === 'sum') {
    const x = await load('core/dsl.ts')
    const r = x.rule('token').inputs({op: x.oneOf('mint', 'transfer', 'burn'), from: x.nat, to: x.nat, value: x.nat})
      .state({supply: 0}).maps({Bal: 0})
      .flags(({op, from, value, Bal}: any) => ({mints: op.is('mint'), transfers: op.is('transfer').and(Bal.at(from).atLeast(value)), burns: op.is('burn').and(Bal.at(from).atLeast(value))}))
      .step(({from, to, value, supply, Bal, mints, transfers, burns}: any) => ({Bal: Bal.each((k: any) => Bal.at(k).minus(x.when(transfers.or(burns).and(k.eq(from)), value, 0)).plus(x.when(mints.or(transfers).and(k.eq(to)), value, 0))), supply: x.when(mints, supply.plus(value), x.when(burns, supply.minus(value), supply))}))
    const sum = r.law('the balances sum to the supply', ({Bal, supply}: any) => Bal.sum().eq(supply))
    const cell = r.law('no balance exceeds the supply', ({Bal, supply}: any) => x.forall((k: any) => Bal.at(k).atMost(supply)))
    item = {id: 'token', machine: r.withSumsOf(sum, cell).machine, laws: [...r.kindLaws(), sum, cell]}
  } else if (name === 'nodes') {
    const x = await load('examples/trees.ts'), r = x.searchTree()
    item = {id: 'tree', machine: r.machine, laws: [...r.kindLaws(), ...x.searchTreeLaws(r)]}
  } else throw Error(`unknown child case ${name}`)
  const machine = JSON.stringify(item.machine)
  const laws = JSON.stringify({laws: item.laws, stepLaws: item.stepLaws})
  const lean = machineOnly ? null : (await load('lean-kernel/emit.ts')).toLean([item])
  // Sentinel allows any incidental emitter logging, without changing emitted bytes.
  console.log('BINDER_COMPAT_RESULT ' + JSON.stringify({machine, laws, lean}))
} else {
  const rev = spawnSync('git', ['-C', baseline, 'rev-parse', 'HEAD'], {encoding: 'utf8'})
  if (rev.status !== 0 || rev.stdout.trim() !== 'c08bb385bbb1afc8dbf6ce1fc8aa8d838b9eb3a5') throw Error(`baseline HEAD is not c08bb385b: ${rev.stdout} ${rev.stderr}`)
  const status = spawnSync('git', ['-C', baseline, 'status', '--porcelain', '--untracked-files=no'], {encoding: 'utf8'})
  if (status.status !== 0 || status.stdout) throw Error(`baseline has tracked modifications: ${status.stdout} ${status.stderr}`)
  let failed = false
  for (const name of selected ? [selected] : cases) {
    const results: any[] = []
    for (const root of [baseline, current]) {
      const run = spawnSync(process.execPath, [script, '--child', root, name, args.includes('--machine-only') ? 'machine' : 'lean'], {cwd: root, encoding: 'utf8', maxBuffer: 128 * 1024 * 1024, timeout: 300_000})
      const line = run.stdout?.split('\n').find((s: string) => s.startsWith('BINDER_COMPAT_RESULT '))
      if (run.status !== 0 || !line) {
        console.error(`${name} ${root}: FAILED status=${run.status} signal=${run.signal} error=${run.error ?? ''}\n${run.stderr}\n${run.stdout}`)
        failed = true; results.push(null); continue
      }
      results.push(JSON.parse(line.slice('BINDER_COMPAT_RESULT '.length)))
    }
    if (!results[0] || !results[1]) continue
    for (const field of ['machine', 'laws', ...(args.includes('--machine-only') ? [] : ['lean'])]) {
      const a = Buffer.from(results[0][field]), b = Buffer.from(results[1][field])
      let i = 0; while (i < a.length && i < b.length && a[i] === b[i]) i++
      if (i === a.length && i === b.length) console.log(`${name} ${field}: IDENTICAL ${a.length} bytes`)
      else {
        failed = true
        const context = (v: Buffer) => JSON.stringify(v.subarray(Math.max(0, i - 80), Math.min(v.length, i + 120)).toString('utf8'))
        console.error(`${name} ${field}: DIFFER at byte ${i}, lengths ${a.length}/${b.length}\n  baseline ${context(a)}\n  current  ${context(b)}`)
      }
    }
  }
  if (failed) process.exitCode = 1
}
