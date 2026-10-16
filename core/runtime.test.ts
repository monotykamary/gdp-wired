// The runtimes' guards and histories: undeclared names refused by the kernel and both runtimes; params and inputs that
// aren't naturals below 2^53, and values past 2^53 - 1, refused at run time; machines with a history compiled to
// JavaScript against the interpreter; and pruning, which may drop records only where the kernel proves they add nothing
// to any query: then a pruned run computes what an unpruned one does, step by step. FUZZ_SEED and FUZZ_SCALE shard it.
import {expect, test} from 'bun:test'
import {type C, type E, type Machine, type State, all, atMost, compileJs, get, interpret, loadJs, ite, less, n, plus, same, times, x} from './machine.ts'
import {windowCeiling, windowLimit} from './models.ts'
import {obligations, scope} from '../kernel/kernel.ts'
import {proveLaws} from '../kernel/prove.ts'

let seed = Number(process.env.FUZZ_SEED ?? 777)
const scale = Number(process.env.FUZZ_SCALE ?? 1)
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const pick = <T>(xs: T[]): T => xs[rand(xs.length)]!
const load = (m: Machine) => loadJs(m)

// --- names ---------------------------------------------------------------------------------------------------------------

const counter: Machine = {
  name: 'counter', params: ['cap'], inputs: ['amount'], state: {used: n(0)}, maps: {Seen: 0},
  step: {flags: {fits: atMost(plus(x('used'), x('amount')), x('cap'))}, state: {used: ite({op: 'flag', name: 'fits'}, plus(x('used'), x('amount')), x('used'))}, maps: {Seen: {key: x('amount'), value: plus(get('Seen', x('amount')), n(1))}}},
}
const law = {name: 'used <= cap', holds: atMost(x('used'), x('cap'))}

test('a name nobody declares is refused by the kernel and by both runtimes', () => {
  expect(proveLaws(counter, [law]).proven).toBe(true)
  const typos: [string, Machine, {name: string, holds: C, forall?: string}][] = [
    ['a law', counter, {name: 'typo', holds: atMost(x('usd'), x('cap'))}],
    ['a law reading a request', counter, {name: 'typo', holds: atMost(x('amount'), x('cap'))}],
    ['a law reading a flag', counter, {name: 'typo', holds: {op: 'flag', name: 'fits'}}],
    ['a step', {...counter, step: {...counter.step, state: {used: plus(x('used'), x('amout'))}}}, law],
    ['a flag', {...counter, step: {...counter.step, flags: {fits: atMost(x('usd'), x('cap'))}}}, law],
    ['a flag read', {...counter, step: {...counter.step, state: {used: ite({op: 'flag', name: 'fit'}, x('used'), n(0))}}}, law],
    ['a map read', {...counter, step: {...counter.step, state: {used: plus(x('used'), get('Sen', n(0)))}}}, law],
    ['a map written', {...counter, step: {...counter.step, maps: {Sen: {key: n(0), value: n(1)}}}}, law],
    ['a state set', {...counter, step: {...counter.step, state: {usd: n(0)}}}, law],
    ['a start value', {...counter, state: {used: x('amount')}}, law],
    ['an assumption', {...counter, assume: atMost(x('amout'), n(5))}, law],
    ['a precondition', {...counter, pre: atMost(x('used'), n(5))}, law],
    ['a name twice', {...counter, inputs: ['amount', 'cap']}, law],
    ['a key named like a param', counter, {name: 'keyed', holds: atMost(get('Seen', x('cap')), n(9)), forall: 'cap'}],
  ]
  for (const [what, m, l] of typos) {
    expect(() => obligations(m, [l]), what).toThrow()
    expect(() => proveLaws(m, [l]), what).toThrow()
    if (what.startsWith('a law') || what.startsWith('a key')) continue
    expect(() => interpret(m), what).toThrow()
    expect(() => compileJs(m), what).toThrow()
  }
  expect(() => scope(counter, [law])).not.toThrow()
})

test('params and inputs must be naturals below 2^53, and values may not pass 2^53 - 1', () => {
  for (const run of [interpret(counter), load(counter)]) {
    const st = run.init({cap: 10})
    for (const bad of [{}, {amount: -1}, {amount: 1.5}, {amount: '3'}, {amount: 2 ** 53}, {amount: NaN}]) expect(() => run.step({cap: 10}, run.init({cap: 10}), bad as never), JSON.stringify(bad)).toThrow(RangeError)
    expect(() => run.init({cap: -2})).toThrow(RangeError)
    expect(() => run.step({cap: 10}, st, {amount: 3, used: 999})).not.toThrow() // a stray input is ignored, never read as the state
    expect(run.step({cap: 10}, run.init({cap: 10}), {amount: 3, used: 999}).scalars.used).toBe(3)
  }
  const doubling: Machine = {name: 'doubling', params: [], inputs: [], state: {v: n(1)}, step: {state: {v: plus(times(2, x('v')), n(1))}}}
  for (const run of [interpret(doubling), load(doubling)]) {
    let st = run.init({}), steps = 0
    expect(() => { for (;;) { st = run.step({}, st, {}); steps++ } }).toThrow(RangeError)
    expect(steps).toBe(52) // v = 2^(k+1) - 1 after k steps: 2^53 - 1 is reached exactly, and the next step would pass it
    expect(st.scalars.v).toBe(Number.MAX_SAFE_INTEGER)
  }
})

// --- histories: compiled against interpreted, and pruning -------------------------------------------------------------

const term = (names: string[], d: number): E => {
  const r = rand(d <= 0 ? 2 : 6)
  if (r === 0) return x(pick(names))
  if (r === 1) return n(rand(3))
  if (r === 2) return plus(term(names, d - 1), term(names, d - 1))
  if (r === 3) return {op: 'sub', a: term(names, d - 1), b: term(names, d - 1)}
  if (r === 4) return {op: 'min', a: term(names, d - 1), b: term(names, d - 1)}
  return ite(cond(names, d - 1), term(names, d - 1), term(names, d - 1))
}
const cond = (names: string[], d: number): C => ({op: (['<', '<=', '='] as const)[rand(3)]!, a: term(names, d), b: term(names, d)})
// Requests (a, t) with t the order; records keep both; u sums a term of the record; the query s counts (or sums) over
// the records, often only those inside a window of width w before t, the shape pruning is for.
function machine(): Machine {
  const fields = ['r.a', 'r.t'], request = ['a', 't', 'p', 'w']
  const windowed = (g: E): E => ite(less(x('t'), plus(x('r.t'), pick([x('w'), x('p'), n(2)]))), g, n(0))
  const query = rand(4) === 0 ? term([...fields, ...request], 2) : windowed(rand(2) ? n(1) : term([...fields, 'a', 'p'], 1))
  return {
    name: 'random history', params: ['p', 'w'], inputs: ['a', 't', 's'], state: {z: n(0)}, maps: {M: 0},
    step: {flags: {open: atMost(x('s'), pick([x('p'), x('w'), plus(x('z'), n(1))]))}, state: {z: plus(x('z'), ite({op: 'flag', name: 'open'}, n(1), n(0)))}, maps: {M: {key: x('a'), value: plus(get('M', x('a')), x('s'))}}},
    history: {keep: rand(4) === 0 ? same(n(0), n(0)) : any2({op: 'flag', name: 'open'}, cond(['a', 'p', 'z'], 1)), record: ['a', 't'], sums: {u: term([...fields, 'p'], 1)}, queries: {s: query},
      prune: {order: 't', after: pick([x('w'), x('p'), n(1), plus(x('w'), n(1))])}},
  }
}
const any2 = (a: C, b: C): C => ({op: 'or', xs: [a, b]})
const unpruned = (m: Machine): Machine => ({...m, history: {...m.history!, prune: undefined}})
const cells = (st: State) => JSON.stringify(Object.fromEntries(Object.entries(st.maps).map(([name, map]) => [name, [...map.entries()].sort((a, b) => a[0] - b[0])])))

test('histories: compiled runs as interpreted, and proven pruning changes nothing', () => {
  let proven = 0, unproven = 0, caught = 0, steps = 0
  for (let trial = 0; trial < 300 * scale; trial++) {
    const m = machine()
    const ok = proveLaws(m, []).proven // with no laws, the goals are the pruning goals
    ok ? proven++ : unproven++
    const params = {p: rand(4), w: 1 + rand(4)}
    const run = interpret(m), full = interpret(unpruned(m)), gen = load(m), genFull = load(unpruned(m))
    let a = run.init(params), b = full.init(params), g = gen.init(params), h = genFull.init(params), t = 0, differs = false
    for (let i = 0; i < 2 + rand(25); i++) {
      t += rand(3)
      const input = {a: rand(4), t}
      // Compiled and interpreted always agree, pruned or not (they prune alike).
      a = run.step(params, a, input), g = gen.step(params, g, input), b = full.step(params, b, input), h = genFull.step(params, h, input)
      expect(g.scalars).toEqual(a.scalars); expect(cells(g)).toBe(cells(a)); expect(g.history!.slice(g.head)).toEqual(a.history!)
      expect(h.scalars).toEqual(b.scalars); expect(cells(h)).toBe(cells(b))
      // Proven pruning: the same as keeping everything.
      if (ok) { expect(a.scalars).toEqual(b.scalars); expect(cells(a)).toBe(cells(b)) }
      else if (JSON.stringify(a.scalars) !== JSON.stringify(b.scalars) || cells(a) !== cells(b)) differs = true
      steps++
    }
    if (!ok && differs) caught++
    // Going back in order is refused by both runtimes.
    if (t > 0) { expect(() => run.step(params, a, {a: 0, t: t - 1})).toThrow(RangeError); expect(() => gen.step(params, g, {a: 0, t: t - 1})).toThrow(RangeError) }
  }
  console.log(`histories: ${proven} with pruning proven, ${unproven} not (${caught} of those caught changing a run), ${steps.toLocaleString()} steps compared`)
  expect(proven).toBeGreaterThan(30 * scale)
  expect(caught).toBeGreaterThan(0) // the test can see pruning that is wrong
}, 600_000)

test('pruning outside the rule is refused', () => {
  const m = machine()
  const bad = (prune: unknown) => () => obligations({...m, history: {...m.history!, prune: prune as {order: string, after: E}}}, [])
  expect(bad({order: 'a2', after: n(1)})).toThrow() // not a recorded input
  expect(bad({order: 's', after: n(1)})).toThrow() // a query
  expect(bad({order: 't', after: x('z')})).toThrow() // reads the state
  expect(bad({order: 't', after: x('a')})).toThrow() // reads the request
  expect(bad({order: 't', after: all(same(n(0), n(0))) as unknown as E})).toThrow() // not a term
})

// --- the sliding-window limit (core/models.ts) -------------------------------------------------------------------------

test('the window limit: proven pruned or not, and its pruned compiled runs equal unpruned interpreted ones', () => {
  expect(proveLaws(windowLimit(), [windowCeiling]).proven).toBe(true)
  expect(proveLaws(windowLimit(true), [windowCeiling]).proven).toBe(true)
  let events = 0
  for (let trial = 0; trial < 300 * scale; trial++) {
    const p = {w: 1 + rand(5), c: rand(4)}
    const ends = [0, 3, 6, 10, 15].map(now => {
      const params = {...p, now}, gen = load(windowLimit(true)), run = interpret(windowLimit())
      return {params, gen, run, g: gen.init(params), st: run.init(params)}
    })
    let t = 0
    for (let e = 0; e < 1 + rand(30); e++) {
      t += rand(3)
      const input = {forced: rand(5) === 0 ? 1 : 0, t}
      for (const end of ends) {
        end.g = end.gen.step(end.params, end.g, input)
        end.st = end.run.step(end.params, end.st, input)
        expect(end.g.scalars).toEqual(end.st.scalars)
        expect(end.g.scalars.ours!).toBeLessThanOrEqual(p.c)
        expect(end.g.history!.length - end.g.head!).toBeLessThanOrEqual(end.st.history!.length)
      }
      events++
    }
  }
  console.log(`window limit: ${events.toLocaleString()} ordered events × 5 window ends, pruned compiled = unpruned interpreted, ceiling held`)
})
