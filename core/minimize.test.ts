// minimizeRun: the run returned breaks the law on the rule, and no run with one request removed does.
import {expect, setDefaultTimeout, test} from 'bun:test'
import {forall, when, minimizeRun, minimizeRunDetailed, nat, oneOf, rule} from './dsl.ts'
import {type Request, type State, interpret} from './machine.ts'
import {allowed, watch} from './watch.ts'
import {corpus as items} from '../research/realworld/corpus.ts'
import results from '../research/realworld/results.json'
import {invariantInput} from '../research/realworld/lib.ts'

// (the corpus replays take 8 s on a 2 vCPU VM: past bun's 5 s default)
setDefaultTimeout(120_000)

type AnyRule = Parameters<typeof minimizeRun>[0] & {machine: import('./machine.ts').Machine}
type Shown = Record<string, unknown>
const wire = (s: Shown): Request => Object.fromEntries(Object.entries(s).map(([n, x]) => [n, typeof x === 'number' ? x : new Map(Object.entries(x as Record<string, number>).map(([k, v]) => [Number(k), v]))])) as Request
// An independent replay: `strict` stops at a refused request (core/bmc.ts's replay), else skips it.
const breaks = (r: AnyRule, law: Parameters<typeof watch>[2], params: Record<string, number>, trace: readonly Shown[], strict: boolean): boolean => {
  const m = r.machine, it = interpret(m), on = watch(m, it, law, params, 8)
  let st: State = it.init(params)
  if (!on.start(st)) return true
  for (const s of trace) {
    const input = wire(s)
    let next: State | undefined
    try { next = allowed(m, it, params, st, input) ? it.step(params, st, input) : undefined } catch (e) { if (!(e instanceof RangeError)) throw e }
    if (!next) { if (strict) return false; continue }
    if (!on.step(st, input, next)) return true
    st = next
  }
  return false
}
const oneMinimal = (r: AnyRule, law: Parameters<typeof watch>[2], params: Record<string, number>, trace: readonly Shown[]) => {
  for (const strict of [true, false]) {
    expect(breaks(r, law, params, trace, strict)).toBe(true)
    for (let i = 0; i < trace.length; i++) expect(breaks(r, law, params, trace.filter((_, j) => j !== i), strict)).toBe(false)
  }
}

// A counter with a cap that `burst` steps over, a lock that must be opened first, and requests that change nothing
// (`noop`) or only an unrelated count (`tick`).
const gate = () => rule('gate')
  .params({cap: nat})
  .inputs({op: oneOf('noop', 'tick', 'unlock', 'lock', 'add', 'burst', 'reset'), n: nat})
  .state({used: 0, open: 0, ticks: 0})
  .step(({op, n, used, open, ticks, cap}) => ({
    ticks: when(op.is('tick'), ticks.plus(1), ticks),
    open: when(op.is('unlock'), 1, when(op.is('lock'), 0, open)),
    used: when(op.is('reset'), 0, when(op.is('add').and(used.plus(n).atMost(cap)), used.plus(n), when(op.is('burst').and(open.eq(1), used.gt(0)), used.plus(n), used))),
  }))

test('a padded run comes down to the three requests that matter', () => {
  const r = gate(), law = r.law('within the cap', ({used, cap}) => used.atMost(cap)), params = {cap: 5}
  const enc = (op: string, n = 0) => (r as never as {encodeInput: (i: unknown) => Record<string, number>}).encodeInput({op, n})
  const pad = (i: number) => (i % 3 === 0 ? enc('noop', i % 7) : i % 3 === 1 ? enc('tick') : i % 2 ? enc('lock') : enc('reset'))
  const trace: Record<string, number>[] = []
  for (let i = 0; i < 2500; i++) trace.push(pad(i))
  trace.push(enc('add', 2))
  for (let i = 0; i < 1500; i++) trace.push(i % 2 ? enc('noop', i % 5) : enc('tick'))
  trace.push(enc('unlock'), enc('add', 1))
  for (let i = 0; i < 1000; i++) trace.push(i % 2 ? enc('noop') : enc('tick'))
  trace.push(enc('burst', 9))
  for (let i = 0; i < 500; i++) trace.push(enc('tick'))
  expect(breaks(r as never, law, params, trace, true)).toBe(true)
  const t0 = performance.now(), out = minimizeRunDetailed(r as never, law, {params, trace})
  console.log(`padded: ${trace.length} -> ${out.to} requests, ${out.replays} replays, ${out.steps} steps, ${(performance.now() - t0).toFixed(1)} ms`)
  expect(out.minimal).toBe(true)
  expect(out.run.trace.length).toBe(3)
  expect(out.run.params).toEqual(params)
  for (const s of out.run.trace) expect(trace.includes(s as Record<string, number>)).toBe(true)
  oneMinimal(r as never, law, params, out.run.trace)
  // The requests alone, with the params beside them; and the rule's own values.
  const alone = minimizeRun(r as never, law, trace, {params})
  expect(Array.isArray(alone) && alone.length).toBe(3)
  const named = minimizeRun(r as never, law, [{op: 'unlock', n: 0}, {op: 'tick', n: 0}, {op: 'add', n: 3}, {op: 'burst', n: 3}], {params})
  expect(named).toEqual([{op: 'unlock', n: 0}, {op: 'add', n: 3}, {op: 'burst', n: 3}])
})

test('a tiny budget still returns a breaking run; a run that breaks nothing is refused', () => {
  const r = gate(), law = r.law('within the cap', ({used, cap}) => used.atMost(cap)), params = {cap: 5}
  const enc = (op: string, n = 0) => (r as never as {encodeInput: (i: unknown) => Record<string, number>}).encodeInput({op, n})
  const trace = [...Array.from({length: 3000}, (_, i) => enc('tick', i)), enc('unlock'), enc('add', 1), enc('burst', 9), enc('tick')]
  const out = minimizeRunDetailed(r as never, law, {params, trace}, {ms: 0})
  expect(breaks(r as never, law, params, out.run.trace, true)).toBe(true)
  expect(out.run.trace.length).toBeLessThanOrEqual(3003)
  expect(() => minimizeRun(r as never, law, {params, trace: trace.slice(0, 3000)})).toThrow(/does not break/)
})

test('a law about every key, and a step law', () => {
  const r = rule('seats').inputs({op: oneOf('take', 'free', 'idle'), k: nat}).state({taken: 0}).maps({Seat: 0})
    .step(({op, k, taken, Seat}) => ({
      taken: when(op.is('take'), taken.plus(1), when(op.is('free').and(taken.gt(0)), taken.minus(1), taken)),
      Seat: Seat.set(k, when(op.is('take'), 1, when(op.is('free'), 0, Seat.at(k)))),
    }))
  const enc = (op: string, k = 0) => (r as never as {encodeInput: (i: unknown) => Record<string, number>}).encodeInput({op, k})
  const law = r.law('a taken seat is counted', ({Seat, taken}) => forall(k => Seat.at(k).eq(1).implies(taken.atLeast(1))))
  const trace = [enc('idle', 4), enc('take', 40), enc('take', 41), enc('idle'), enc('free', 7), enc('take', 9), enc('free', 3), enc('free', 2), enc('free', 1), enc('idle')]
  const out = minimizeRun(r as never, law, {params: {}, trace})
  expect(out.trace.length).toBe(2)
  oneMinimal(r as never, law, {}, out.trace)
  const sl = r.stepLaw('freeing lowers the count', ({taken}, after) => after.taken.lt(taken), ({op}) => op.is('free'))
  const out2 = minimizeRun(r as never, sl, {params: {}, trace})
  expect(out2.trace.length).toBe(1)
  oneMinimal(r as never, sl, {}, out2.trace)
})

test('the recorded refutations of the real-world corpus (results.json), as they are and padded', () => {
  const rows = (results as {item: string, law: number, run?: {params: Record<string, number>, trace: Shown[]}}[]).filter(x => x.run)
  let seen = 0
  for (const row of rows) {
    const input = invariantInput(items.find(i => i.id === row.item)!.laws[row.law]!)
    if (!input) continue
    const [r, law] = input, run = row.run!
    if (!breaks(r as never, law, run.params, run.trace, true)) continue // (the corpus moved on since the recorded run)
    seen++
    const out = minimizeRunDetailed(r as never, law, run)
    expect(out.minimal).toBe(true)
    oneMinimal(r as never, law, run.params, out.run.trace)
    // Padded: before each request, the requests of the run that leave the state there as it is (the rule's own).
    const m = (r as AnyRule).machine, it = interpret(m), padded: Shown[] = []
    let st = it.init(run.params)
    for (const s of run.trace) {
      for (let c = 0; c < 40; c++) for (const p of run.trace) {
        let next: State | undefined
        try { next = allowed(m, it, run.params, st, wire(p)) ? it.step(run.params, st, wire(p)) : undefined } catch { next = undefined }
        if (next && JSON.stringify([next.scalars, Object.entries(next.maps).map(([n, c]) => [n, [...c]]), next.history, next.last]) === JSON.stringify([st.scalars, Object.entries(st.maps).map(([n, c]) => [n, [...c]]), st.history, st.last])) padded.push(p)
      }
      padded.push(s)
      st = it.step(run.params, st, wire(s))
    }
    const t0 = performance.now(), wide = minimizeRunDetailed(r as never, law, {params: run.params, trace: padded}, {ms: 60_000}), ms = performance.now() - t0
    console.log(`${row.item} #${row.law}: ${run.trace.length} -> ${out.to} in ${out.ms.toFixed(1)} ms; padded ${padded.length} -> ${wide.to} in ${ms.toFixed(1)} ms`)
    expect(wide.minimal).toBe(true)
    expect(wide.to).toBeLessThanOrEqual(out.to)
    oneMinimal(r as never, law, run.params, wide.run.trace)
  }
  expect(seen).toBeGreaterThan(3)
})
