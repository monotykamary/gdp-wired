// Histories by brute force: random machines with a history (a sum u, a query s, relations between them, a counter z
// guarded by the query); whenever the kernel accepts a law's proof, no run of the interpreter (which keeps the history) from
// the start may break it, nor the relations the proof assumed. FUZZ_SEED and FUZZ_SCALE shard it as kernel.test.ts.
import {expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, evalC, interpret} from '../core/machine.ts'
import {historyMachine} from './kernel.ts'
import {proveLaws} from './prove.ts'

let seed = Number(process.env.FUZZ_SEED ?? 777)
const scale = Number(process.env.FUZZ_SCALE ?? 1)
const rand = (n: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * n) }
const x = (name: string): E => ({op: 'var', name}), n = (value: number): E => ({op: 'const', value})
const pick = <T>(xs: T[]): T => xs[rand(xs.length)]!
const term = (names: string[], d: number): E => {
  const r = rand(d <= 0 ? 2 : 7)
  if (r === 0) return x(pick(names))
  if (r === 1) return n(rand(3))
  if (r === 2) return {op: 'add', a: term(names, d - 1), b: term(names, d - 1)}
  if (r === 3) return {op: 'sub', a: term(names, d - 1), b: term(names, d - 1)}
  if (r === 4) return {op: 'min', a: term(names, d - 1), b: term(names, d - 1)}
  if (r === 5) return {op: 'mul', k: 2, a: term(names, d - 1)}
  return {op: 'if', c: cond(names, d - 1), then: term(names, d - 1), else: term(names, d - 1)}
}
const cond = (names: string[], d: number): C => {
  const r = rand(5)
  if (r === 3) return {op: 'not', x: cond(names, d)}
  if (r === 4 && d > 0) return {op: rand(2) ? 'and' : 'or', xs: [cond(names, d - 1), cond(names, d - 1)]}
  return {op: (['<', '<=', '='] as const)[rand(3)]!, a: term(names, d), b: term(names, d)}
}
const le = (a: E, b: E): C => ({op: '<=', a, b}), plus = (a: E, b: E): E => ({op: 'add', a, b}), twice = (a: E): E => ({op: 'mul', k: 2, a})

function machine(): {m: Machine, law: Law} {
  const record = ['r.a', 'r.b'], request = ['a', 'b', 'p', 'q']
  const relations = Array.from({length: rand(3)}, () => ({when: cond(request, 1), holds: pick([le(x('u'), x('s')), le(x('s'), x('u')), le(twice(x('u')), x('s')), le(x('u'), plus(x('s'), x('s')))])}))
  const m: Machine = {
    name: 'random history', params: ['p', 'q'], inputs: ['a', 'b', 's'], state: {z: n(0)},
    step: {state: {z: plus(x('z'), {op: 'if', c: {op: 'and', xs: [cond(['a', 'b', 'p', 'q'], 1), le(plus(x('s'), n(1)), pick([x('p'), x('q'), n(2)]))]}, then: n(1), else: n(0)})}},
    history: {keep: cond(['a', 'b', 's', 'p', 'z'], 1), record: ['a', 'b'], sums: {u: term([...record, 'p'], 1)}, queries: {s: term([...record, ...request], 1)}, relations},
  }
  const law: Law = {name: 'random law', holds: pick([le(x('z'), x('u')), le(x('z'), x('p')), le(x('u'), plus(x('p'), x('q'))), le(x('z'), plus(x('u'), x('q'))), le(x('u'), n(2)), le(x('z'), n(1))])}
  return {m, law}
}

// The release ceiling's shape: a request is kept unguarded (K1) or when the query is under p (K2 and s + 1 <= p); u
// counts the guarded records that meet C; the query counts every record that meets C or E. So u <= p needs the
// relation u <= s, which holds record by record, unless a mutation (a random query, a random `when`) breaks it.
const rename = <T>(t: T): T => JSON.parse(JSON.stringify(t).replace(/"name":"([ab])"/g, '"name":"r.$1"'))
function ceiling(): {m: Machine, law: Law} {
  const k1 = cond(['a', 'b'], 1), k2 = cond(['a', 'b', 'q'], 1), c = cond(['a', 'b'], 1), e = cond(['a', 'b', 'p', 'q'], 1)
  const ours: C = {op: 'and', xs: [{op: 'not', x: k1}, c]}
  const one = (cc: C): E => ({op: 'if', c: cc, then: n(1), else: n(0)})
  const query = rand(4) === 0 ? term(['r.a', 'r.b', 'a', 'b', 'p'], 1) : one({op: 'or', xs: [rename(ours), rename(e)]})
  const when = rand(3) === 0 ? cond(['a', 'b', 'p', 'q'], 1) : le(n(0), n(0))
  const m: Machine = {
    name: 'random ceiling', params: ['p', 'q'], inputs: ['a', 'b', 's'], state: {},
    step: {},
    history: {keep: {op: 'or', xs: [k1, {op: 'and', xs: [k2, le(plus(x('s'), n(1)), x('p'))]}]}, record: ['a', 'b'], sums: {u: one(rename(ours))}, queries: {s: query},
      relations: rand(5) === 0 ? [] : [{when, holds: le(x('u'), x('s'))}]},
  }
  return {m, law: {name: 'u <= p', holds: le(x('u'), x('p'))}}
}

test('a law proven over a history holds on every run', () => {
  let proven = 0, runs = 0, needed = 0
  for (let trial = 0; trial < 400 * scale; trial++) {
    const {m, law} = trial % 2 ? machine() : ceiling()
    const r = proveLaws(m, [law])
    if (!r.proven || !r.checked) continue
    proven++
    if (m.history!.relations!.length && !proveLaws({...m, history: {...m.history!, relations: []}}, [law]).proven) needed++
    const run = interpret(m)
    for (let p = 0; p < 3; p++) for (let q = 0; q < 3; q++) {
      const params = {p, q}
      const walk = (st: ReturnType<typeof run.init>, depth: number) => {
        runs++
        expect(evalC(law.holds, params, st, m)).toBe(true)
        if (depth === 3) return
        for (let a = 0; a < 3; a++) for (let b = 0; b < 3; b++) {
          const input = {a, b}
          const s = run.queries(params, st, input).s!
          for (const rel of m.history!.relations ?? []) if (evalC(rel.when, {...params, ...input}, st, m)) expect(evalC(rel.holds, {...params, ...input, s}, st, m)).toBe(true)
          walk(run.step(params, st, input), depth + 1)
        }
      }
      walk(run.init(params), 0)
    }
  }
  console.log(`histories: ${proven} of ${400 * scale} random laws proven (${needed} only with their relations), ${runs.toLocaleString()} states checked`)
  expect(proven).toBeGreaterThan(20 * scale)
  expect(needed).toBeGreaterThan(0)
}, 600_000)

test('a history outside the rule is refused', () => {
  const base = machine().m
  const bad = (h: Partial<NonNullable<Machine['history']>>) => () => historyMachine({...base, history: {...base.history!, ...h}})
  expect(bad({relations: [{when: le(n(0), n(0)), holds: le(x('u'), plus(x('s'), n(1)))}]})).toThrow() // a constant: not homogeneous
  expect(bad({relations: [{when: le(x('z'), n(0)), holds: le(x('u'), x('s'))}]})).toThrow() // when reads the state
  expect(bad({relations: [{when: le(x('s'), n(0)), holds: le(x('u'), x('s'))}]})).toThrow() // when reads a query
  expect(bad({sums: {u: x('a')}})).toThrow() // a sum reads the request, not the record
  expect(bad({queries: {s: x('s')}})).toThrow() // a query reads a query
  expect(bad({record: ['s']})).toThrow() // a query recorded
  expect(bad({sums: {z: x('r.a')}})).toThrow() // a sum named like a state variable
  expect(() => historyMachine({...base, params: ['p', 'r.a']})).toThrow() // a param named like a record field
  expect(() => historyMachine({...base, state: {...base.state, 'r.b': n(0)}})).toThrow() // a state variable named like one
})
