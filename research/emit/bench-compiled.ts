// Paired same-VM timing and parity benchmark for `compiled()` BEFORE (`f53981041`) vs AFTER (Phase 2 shared
// `core/codegen.ts` printer), run in BOTH forward (before -> after) and reverse (after -> before) order.
import {readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {bool, min, nat, rule, when} from '../../core/dsl.ts'
import {type Compiled, type Machine, type Request, type State, compileFunction, compileJs, interpret, loadJs, seeded} from '../../core/machine.ts'
import {accounts} from '../../examples/datatypes.ts'
import {protocols} from '../protocols/models.ts'

const beforeMap = JSON.parse(readFileSync(join(import.meta.dir, 'before-compiled.json'), 'utf8')) as Record<string, string>

function loadFromJs(src: string): Compiled {
  return compileFunction<() => Compiled>([], `${src.replace(/^export function/gm, 'function')}\nreturn {init, fork, step}`)()
}

type BenchCase = {
  name: string
  machine: Machine
  params: Record<string, number>
  steps: number
  inputs: Request[]
}

function makeTraces(): BenchCase[] {
  const rand = seeded(1337)
  const budget = rule('budget').params({b: nat, m: nat}).inputs({c: nat}).state({s: 0})
    .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
  const caps = rule('caps').params({d: nat}).inputs({acct: nat, day: nat, ok: bool}).maps({Acct: 0, Day: 0})
    .flags(({ok, acct, day, d, Acct, Day}) => ({granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d))}))
    .step(({acct, day, granted, Acct, Day}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted)}))
  const acc = accounts()
  const byId = Object.fromEntries(protocols.map(p => [p.id, p]))
  const lockSync = byId.lock_server_sync!.make()
  const twoPC = byId.two_phase_commit!.make()

  const gen = (n: number, f: () => Request): Request[] => Array.from({length: n}, f)
  return [
    {
      name: 'budget',
      machine: budget.machine,
      params: {b: 1_000_000, m: 50},
      steps: 150_000,
      inputs: gen(4096, () => ({c: rand(100)})),
    },
    {
      name: 'caps',
      machine: caps.machine,
      params: {d: 500},
      steps: 80_000,
      inputs: gen(4096, () => ({acct: rand(512), day: rand(64), ok: rand(2)})),
    },
    {
      name: 'accounts',
      machine: acc.machine,
      params: {},
      steps: 80_000,
      inputs: gen(4096, () => ({op: rand(3), who: rand(128), amount: rand(100)})),
    },
    {
      name: 'lock_server_sync',
      machine: lockSync.machine,
      params: {},
      steps: 80_000,
      inputs: gen(4096, () => ({op: rand(2), x: rand(16), y: rand(16)})),
    },
    {
      name: 'two_phase_commit',
      machine: twoPC.machine,
      params: {size: 8},
      steps: 30_000,
      inputs: gen(4096, () => ({op: rand(7), n: rand(8), w: rand(8)})),
    },
  ]
}

function runSteps(comp: Compiled, params: Record<string, number>, inputs: Request[], steps: number): State {
  let st = comp.init(params)
  const mask = inputs.length - 1
  for (let i = 0; i < steps; i++) st = comp.step(params, st, inputs[i & mask]!)
  return st
}

function stateSig(st: State): string {
  const maps = Object.fromEntries(Object.entries(st.maps).sort().map(([k, m]) => [k, [...m.entries()].sort((a, b) => a[0] - b[0])]))
  return JSON.stringify({scalars: st.scalars, maps, defaults: st.defaults ?? {}})
}

const median = (xs: number[]): number => {
  const s = [...xs].sort((a, b) => a - b)
  const mid = s.length >> 1
  return s.length % 2 ? s[mid]! : (s[mid - 1]! + s[mid]!) / 2
}
const mean = (xs: number[]): number => xs.reduce((a, b) => a + b, 0) / xs.length

const rounds = Number(process.env.BENCH_ROUNDS ?? '9')
const results: Record<string, unknown>[] = []

for (const c of makeTraces()) {
  const beforeJs = beforeMap[c.name]
  if (!beforeJs) throw new Error(`missing before snapshot for ${c.name}`)
  const afterJs = compileJs(c.machine)
  const jsIdentical = afterJs === beforeJs
  if (!jsIdentical) throw new Error(`${c.name}: compileJs output differed from BEFORE snapshot!`)

  const beforeComp = loadFromJs(beforeJs)
  const afterComp = loadJs(c.machine)
  const interp = interpret(c.machine)

  // Parity check against interpreter on 200 steps
  let sI = interp.init(c.params), sB = beforeComp.init(c.params), sA = afterComp.init(c.params)
  for (let i = 0; i < 200; i++) {
    const req = c.inputs[i]!
    sI = interp.step(c.params, sI, req)
    sB = beforeComp.step(c.params, sB, req)
    sA = afterComp.step(c.params, sA, req)
  }
  const sigI = stateSig(sI), sigB = stateSig(sB), sigA = stateSig(sA)
  if (sigI !== sigB || sigI !== sigA) throw new Error(`${c.name}: parity mismatch against interpreter`)

  // Warmup
  for (let w = 0; w < 2; w++) {
    runSteps(beforeComp, c.params, c.inputs, Math.min(c.steps, 5000))
    runSteps(afterComp, c.params, c.inputs, Math.min(c.steps, 5000))
  }

  const measure = (comp: Compiled): number => {
    const t0 = performance.now()
    const st = runSteps(comp, c.params, c.inputs, c.steps)
    const dt = performance.now() - t0
    if (!st.scalars) throw new Error('unreachable')
    return dt
  }

  // Forward order: before -> after
  const fwdBefore: number[] = [], fwdAfter: number[] = []
  for (let r = 0; r < rounds; r++) {
    fwdBefore.push(measure(beforeComp))
    fwdAfter.push(measure(afterComp))
  }
  // Reverse order: after -> before
  const revBefore: number[] = [], revAfter: number[] = []
  for (let r = 0; r < rounds; r++) {
    revAfter.push(measure(afterComp))
    revBefore.push(measure(beforeComp))
  }

  const row = {
    name: c.name,
    steps: c.steps,
    rounds,
    jsBytes: afterJs.length,
    jsIdentical,
    parityOk: true,
    forward: {
      beforeMedianMs: Number(median(fwdBefore).toFixed(3)),
      afterMedianMs: Number(median(fwdAfter).toFixed(3)),
      ratio: Number((median(fwdAfter) / median(fwdBefore)).toFixed(4)),
      beforeMeanMs: Number(mean(fwdBefore).toFixed(3)),
      afterMeanMs: Number(mean(fwdAfter).toFixed(3)),
    },
    reverse: {
      beforeMedianMs: Number(median(revBefore).toFixed(3)),
      afterMedianMs: Number(median(revAfter).toFixed(3)),
      ratio: Number((median(revAfter) / median(revBefore)).toFixed(4)),
      beforeMeanMs: Number(mean(revBefore).toFixed(3)),
      afterMeanMs: Number(mean(revAfter).toFixed(3)),
    },
  }
  results.push(row)
  console.log(`${c.name.padEnd(18)} steps=${c.steps} jsIdentical=${jsIdentical} fwd=${row.forward.beforeMedianMs}ms->${row.forward.afterMedianMs}ms (${row.forward.ratio}x) rev=${row.reverse.beforeMedianMs}ms->${row.reverse.afterMedianMs}ms (${row.reverse.ratio}x)`)
}

const outDir = process.env.SUPERCOMPUTER_OUTPUT_DIR
if (outDir) {
  writeFileSync(join(outDir, 'paired-timings.json'), JSON.stringify({rounds, results}, null, 2))
}
