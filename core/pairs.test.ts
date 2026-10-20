// Conditions at every two keys or more (core/dsl.ts everyKey((i, j) => ...)): random conditions over keys in key terms,
// compared with each other plainly, decided by the runtimes on every tuple of a few keys per breakpoint, against brute
// force over every tuple up to well past every cell and value, interpreted and compiled. Then examples/pairs.ts proven and
// its broken variants refused, what the kernel refuses, and a fuzz: every law over two keys the kernel accepts holds on
// every run.
import {expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, type Request, interpret, loadJs} from './machine.ts'
import {watch} from './watch.ts'
import {proveLaws} from '../kernel/prove.ts'
import {everyKey, nat, proveSteps, rule} from './dsl.ts'
import {scope} from '../kernel/kernel.ts'
import {distinctNames, distinctNamesLaws, sortedList, sortedListLaws} from '../examples/pairs.ts'

let seed = 23
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const v = (name: string): E => ({op: 'var', name}), c = (value: number): E => ({op: 'const', value})
const pick = <T>(xs: T[]): T => xs[rand(xs.length)]!
// A key term over one of the keys, with an offset from the request or a constant (plainly, the key alone).
const keyTerm = (key: string, plain: boolean): E => (plain ? v(key) : pick<() => E>([
  () => v(key),
  () => ({op: 'add', a: v(key), b: pick([v('a'), c(rand(4))])}),
  () => ({op: 'add', a: pick([v('b'), c(rand(4))]), b: v(key)}),
  () => ({op: 'sub', a: v(key), b: pick([v('a'), c(rand(4))])}),
])())
const cond = (keys: string[], plain: boolean, depth: number, cross = false): C => {
  const atom = (): E => pick<() => E>([() => ({op: 'get', map: pick(['I', 'J']), key: keyTerm(pick(keys), plain)}), () => v(pick(['a', 'b'])), () => c(rand(5))])()
  if (depth === 0 || rand(3) === 0) {
    const op = pick(['<', '<=', '='] as const), [x, y] = [pick(keys), pick(keys)]
    // Two keys compared plainly, a key term compared with a term that reads no key, or two reads (plain trials: the
    // keys only as a map's key, and compared with each other or not at all).
    const r = plain ? (cross ? pick([0, 2, 2]) : 2) : rand(3)
    return r === 0 && x !== y ? {op, a: v(x), b: v(y)} : r === 1 ? {op, a: keyTerm(x, false), b: pick([v('a'), v('b'), c(rand(12))])} : {op, a: atom(), b: atom()}
  }
  return pick<() => C>([() => ({op: 'and', xs: [cond(keys, plain, depth - 1, cross), cond(keys, plain, depth - 1, cross)]}), () => ({op: 'or', xs: [cond(keys, plain, depth - 1, cross), cond(keys, plain, depth - 1, cross)]}),
    () => ({op: 'not', x: cond(keys, plain, depth - 1, cross)})])()
}

type Env = Record<string, number>
const evalBrute = (e: E, env: Env, I: Map<number, number>, J: Map<number, number>): number => {
  switch (e.op) {
    case 'var': return env[e.name]!
    case 'const': return e.value
    case 'add': return evalBrute(e.a, env, I, J) + evalBrute(e.b, env, I, J)
    case 'sub': return Math.max(0, evalBrute(e.a, env, I, J) - evalBrute(e.b, env, I, J))
    case 'get': return (e.map === 'I' ? I : J).get(evalBrute(e.key, env, I, J)) ?? 0
    case 'if': case 'max': case 'min': case 'mul': case 'prod': throw new Error(e.op)
  }
}
const holdsBrute = (x: C, env: Env, I: Map<number, number>, J: Map<number, number>): boolean => {
  switch (x.op) {
    case 'and': return x.xs.every(y => holdsBrute(y, env, I, J))
    case 'or': return x.xs.some(y => holdsBrute(y, env, I, J))
    case 'not': return !holdsBrute(x.x, env, I, J)
    case '<': return evalBrute(x.a, env, I, J) < evalBrute(x.b, env, I, J)
    case '<=': return evalBrute(x.a, env, I, J) <= evalBrute(x.b, env, I, J)
    case '=': return evalBrute(x.a, env, I, J) === evalBrute(x.b, env, I, J)
    case 'all': case 'flag': throw new Error(x.op)
  }
}
const randomMap = () => new Map(Array.from({length: rand(4)}, () => [rand(16), 1 + rand(5)] as const))

// Every tuple up to `top` (cells below 16, values below 12 and offsets below 6 keep every breakpoint below 40, so past
// that every read is a default and only the keys' order is left, which a few keys past 40 show).
const bruteAll = (body: C, keys: string[], top: number, env: Env, I: Map<number, number>, J: Map<number, number>): boolean => {
  const go = (i: number, at: Env): boolean => (i === keys.length ? holdsBrute(body, at, I, J) : Array.from({length: top + 1}, (_, k) => k).every(k => go(i + 1, {...at, [keys[i]!]: k})))
  return go(0, env)
}

test('a condition at every two keys or three: decided on a few keys per breakpoint, as brute force decides it', () => {
  let trues = 0, falses = 0
  for (let trial = 0; trial < 500; trial++) {
    const keys = trial % 10 === 9 ? ['k', 'j', 'h'] : ['k', 'j'], plain = trial % 4 < 2, body = cond(keys, plain, 3, trial % 4 === 1)
    const m: Machine = {name: 'pairs', params: [], inputs: ['a', 'b'], state: {r: c(0)}, inputMaps: ['I', 'J'],
      step: {flags: {f: {op: 'all', key: keys[0]!, keys: keys.slice(1), c: body}}, state: {r: {op: 'if', c: {op: 'flag', name: 'f'}, then: c(1), else: c(0)}}}}
    const run = interpret(m), gen = loadJs(m)
    for (let i = 0; i < 4; i++) {
      const env = {a: rand(6), b: rand(6)}, I = randomMap(), J = randomMap()
      const want = bruteAll(body, keys, keys.length === 3 ? 44 : 60, env, I, J), input = {...env, I, J}
      expect(run.step({}, run.init({}), input).scalars.r, JSON.stringify({body, env, I: [...I], J: [...J]})).toBe(want ? 1 : 0)
      expect(gen.step({}, gen.init({}), input).scalars.r).toBe(want ? 1 : 0)
      if (want) trues++; else falses++
    }
  }
  expect(trues).toBeGreaterThan(100)
  expect(falses).toBeGreaterThan(100)
}, 120_000)

test('a sorted list and distinct names: proven, cross-checked, the broken variants refused', () => {
  for (const [r, laws] of [[sortedList(), sortedListLaws], [distinctNames(), distinctNamesLaws]] as const) {
    const ls = laws(r as never)
    expect(proveSteps(r, ls, [])).toMatchObject({proven: true, checked: true})
    expect((r as ReturnType<typeof sortedList>).crossCheck(ls, []).failure).toBeUndefined()
  }
  expect(proveSteps(sortedList('checks every place but the last'), sortedListLaws(sortedList('checks every place but the last')), []).proven).toBe(false)
  expect(proveSteps(distinctNames('compares each place with the first only'), distinctNamesLaws(distinctNames('compares each place with the first only')), []).proven).toBe(false)
  // Run: an increasing list is taken, one that isn't (or repeats a value) is not.
  const r = sortedList(), g = r.compiled(), lens: number[] = []
  let st = g.init({})
  for (const l of [[1, 2, 3], [3, 2], [0, 0], [5], [1, 4, 9, 9], [2, 7, 8, 20]]) { st = g.step({}, st, r.encodeInput({n: l.length, New: new Map(l.map((x, i) => [i, x]))} as never)); lens.push(st.scalars.len!) }
  expect(lens).toEqual([3, 3, 3, 1, 1, 4])
  expect([...st.maps.At!].filter(([, x]) => x)).toEqual([[0, 2], [1, 7], [2, 8], [3, 20]])
})

test('each key read on its own, compared with another plainly', () => {
  const at = (key: E): E => ({op: 'get', map: 'I', key}), m = (body: C): Machine => ({name: 'pairs', params: [], inputs: ['a'], state: {r: c(0)}, inputMaps: ['I'],
    step: {flags: {f: {op: 'all', key: 'k', keys: ['j'], c: body}}, state: {r: {op: 'if', c: {op: 'flag', name: 'f'}, then: c(1), else: c(0)}}}})
  const proves = (body: C) => () => scope(m(body))
  expect(proves({op: '<=', a: at({op: 'add', a: v('k'), b: v('j')}), b: c(1)})).toThrow(/each read on their own/)
  expect(proves({op: '<', a: v('k'), b: {op: 'add', a: v('j'), b: c(1)}})).toThrow(/each read on their own/)
  expect(proves({op: '<', a: at(v('k')), b: v('j')})).toThrow(/each read on their own/)
  expect(proves({op: '<=', a: at(v('k')), b: {op: 'add', a: v('j'), b: v('k')}})).toThrow(/read only in a map's key or a comparison/)
  expect(proves({op: 'or', xs: [{op: '<', a: v('k'), b: v('j')}, {op: '<=', a: at(v('k')), b: at(v('j'))}]})).not.toThrow()
  expect(() => rule('x').inputs({a: nat}).carries('I').flags(({I}) => ({f: everyKey(k => everyKey(j => I.at(k).atMost(I.at(j))))}))
    .step(() => ({})).machine).toThrow(/two keys at once are named together/)
})

// Soundness: a set S kept by the machine and a list I the request carries; a flag at every two keys guarding writes at
// every key; random laws about every two keys. Whenever the kernel accepts, no run breaks a law.
test('a law over two keys the kernel accepts holds on every run', () => {
  const at = (map: string, key: E): E => ({op: 'get', map, key})
  // An order between the two keys, and a comparison between their values: the flag's and the law's alike half the time.
  const orders = (a: E, b: E): C[] => [{op: '<', a, b}, {op: '<=', a, b}, {op: 'not', x: {op: '=', a, b}}]
  const cmps = (a: E, b: E): C[] => [{op: '<=', a, b}, {op: '<', a, b}, {op: 'not', x: {op: '=', a, b}}]
  let proven = 0, refutedRuns = 0
  for (let trial = 0; trial < 160; trial++) {
    const o = rand(3), k = rand(3), alike = rand(2) === 0
    const guard: C = rand(4) ? {op: 'flag', name: 'q'} : {op: 'not', x: {op: 'flag', name: 'q'}}
    const body: C = {op: 'or', xs: [{op: 'not', x: orders(v('i'), v('j'))[alike ? o : rand(3)]!}, cmps(at('I', v('i')), at(rand(4) ? 'I' : 'S', v('j')))[alike ? k : rand(3)]!]}
    const m: Machine = {name: 'pairs', params: [], inputs: [], state: {n: c(0)}, maps: {S: 0}, inputMaps: ['I'],
      step: {flags: {q: {op: 'all', key: 'i', keys: ['j'], c: body}},
        state: {n: {op: 'if', c: guard, then: {op: 'add', a: v('n'), b: c(1)}, else: v('n')}},
        maps: {S: {each: 'k', value: {op: 'if', c: guard, then: rand(4) ? at('I', v('k')) : {op: 'max', a: at('S', v('k')), b: at('I', v('k'))}, else: at('S', v('k'))}}}}}
    const law: Law = {name: 'random', forall: 'x', keys: ['y'], holds: {op: 'or', xs: [{op: 'not', x: orders(v('x'), v('y'))[o]!}, cmps(at('S', v('x')), at('S', v('y')))[k]!]}}
    const r = proveLaws(m, [law]), run = interpret(m)
    let hit = false
    for (let t = 0; t < 60 && !hit; t++) {
      let st = run.init({})
      const on = watch(m, run, law, {}, 5)
      if (!on.start(st)) { hit = true; break }
      for (let i = 0; i < 5 && !hit; i++) {
        const input: Request = {I: new Map([0, 1, 2, 3].filter(() => rand(3) > 0).map(key => [key, 1 + rand(4)] as const))}
        const before = st
        st = run.step({}, st, input)
        if (!on.step(before, input, st)) hit = true
      }
    }
    if (r.proven && r.checked) { proven++; expect(hit, JSON.stringify({step: m.step, law})).toBe(false) }
    else if (hit) refutedRuns++
  }
  console.log(`pairs fuzz: 160 laws, ${proven} proven (none broken by a run), ${refutedRuns} refused and broken by a run`)
  expect(proven).toBeGreaterThan(10)
  expect(refutedRuns).toBeGreaterThan(10)
}, 600_000)
