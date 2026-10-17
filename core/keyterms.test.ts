// A key read in key terms (k + e, k ∸ e, compared with a term that doesn't read it): the runtimes decide a condition at
// every key, and compute a write at every key, on finitely many breakpoints. Random conditions and values over two maps a
// request carries, against brute force over every key up to well past every cell and value, interpreted and compiled.
import {expect, test} from 'bun:test'
import {type C, type E, type Machine, interpret, loadJs} from './machine.ts'
import {plainKey} from '../kernel/kernel.ts'

let seed = 17
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const v = (name: string): E => ({op: 'var', name}), c = (value: number): E => ({op: 'const', value})
const pick = <T>(xs: T[]): T => xs[rand(xs.length)]!
// A key term over k, with an offset from the request or a constant.
const keyTerm = (): E => pick<() => E>([
  () => v('k'),
  () => ({op: 'add', a: v('k'), b: pick([v('a'), c(rand(4))])}),
  () => ({op: 'add', a: pick([v('b'), c(rand(4))]), b: v('k')}),
  () => ({op: 'sub', a: v('k'), b: pick([v('a'), c(rand(4))])}),
])()
const atom = (): E => pick<() => E>([() => ({op: 'get', map: pick(['I', 'J']), key: keyTerm()}), () => v(pick(['a', 'b'])), () => c(rand(5))])()
const cond = (depth: number): C => {
  if (depth === 0 || rand(3) === 0) {
    const op = pick(['<', '<=', '='] as const)
    // A key term compared with a term that doesn't read the key, or two reads.
    return rand(2) === 0 ? {op, a: keyTerm(), b: pick([v('a'), v('b'), c(rand(12))])} : {op, a: atom(), b: atom()}
  }
  return pick<() => C>([() => ({op: 'and', xs: [cond(depth - 1), cond(depth - 1)]}), () => ({op: 'or', xs: [cond(depth - 1), cond(depth - 1)]}), () => ({op: 'not', x: cond(depth - 1)})])()
}
const value = (depth: number): E => (depth === 0 || rand(2) === 0 ? atom() : {op: 'if', c: cond(1), then: value(depth - 1), else: value(depth - 1)})

// Brute force: every key up to 400 (cells and values stay below 40, so past that every read is a default).
const evalBrute = (e: E, k: number, env: Record<string, number>, I: Map<number, number>, J: Map<number, number>): number => {
  switch (e.op) {
    case 'var': return e.name === 'k' ? k : env[e.name]!
    case 'const': return e.value
    case 'add': return evalBrute(e.a, k, env, I, J) + evalBrute(e.b, k, env, I, J)
    case 'sub': return Math.max(0, evalBrute(e.a, k, env, I, J) - evalBrute(e.b, k, env, I, J))
    case 'if': return holdsBrute(e.c, k, env, I, J) ? evalBrute(e.then, k, env, I, J) : evalBrute(e.else, k, env, I, J)
    case 'get': return (e.map === 'I' ? I : J).get(evalBrute(e.key, k, env, I, J)) ?? 0
    case 'mul': case 'prod': case 'min': case 'max': throw new Error(e.op)
  }
}
const holdsBrute = (x: C, k: number, env: Record<string, number>, I: Map<number, number>, J: Map<number, number>): boolean => {
  switch (x.op) {
    case 'and': return x.xs.every(y => holdsBrute(y, k, env, I, J))
    case 'or': return x.xs.some(y => holdsBrute(y, k, env, I, J))
    case 'not': return !holdsBrute(x.x, k, env, I, J)
    case '<': return evalBrute(x.a, k, env, I, J) < evalBrute(x.b, k, env, I, J)
    case '<=': return evalBrute(x.a, k, env, I, J) <= evalBrute(x.b, k, env, I, J)
    case '=': return evalBrute(x.a, k, env, I, J) === evalBrute(x.b, k, env, I, J)
    case 'all': case 'flag': throw new Error(x.op)
  }
}
const randomMap = () => new Map(Array.from({length: rand(5)}, () => [rand(20), 1 + rand(6)] as const))

test('a condition at every key with its key in key terms: decided on breakpoints, as brute force decides it', () => {
  let trues = 0, falses = 0
  for (let trial = 0; trial < 1500; trial++) {
    const body = cond(3)
    const m: Machine = {name: 'keys', params: [], inputs: ['a', 'b'], state: {r: c(0)}, inputMaps: ['I', 'J'],
      step: {flags: {f: {op: 'all', key: 'k', c: body}}, state: {r: {op: 'if', c: {op: 'flag', name: 'f'}, then: c(1), else: c(0)}}}}
    const run = interpret(m), gen = loadJs(m)
    for (let i = 0; i < 6; i++) {
      const env = {a: rand(6), b: rand(6)}, I = randomMap(), J = randomMap()
      const want = Array.from({length: 401}, (_, k) => k).every(k => holdsBrute(body, k, env, I, J))
      const input = {...env, I, J}
      expect(run.step({}, run.init({}), input).scalars.r, JSON.stringify({body, env, I: [...I], J: [...J]})).toBe(want ? 1 : 0)
      expect(gen.step({}, gen.init({}), input).scalars.r).toBe(want ? 1 : 0)
      if (want) trues++; else falses++
    }
  }
  expect(trues).toBeGreaterThan(100)
  expect(falses).toBeGreaterThan(100)
})

test('a key read plainly is told apart from one in key terms (the GPU searches take only the first)', () => {
  const at = (key: E): E => ({op: 'get', map: 'I', key})
  expect(plainKey({op: '<=', a: at(v('k')), b: c(1)}, 'k')).toBe(true)
  expect(plainKey({op: '<=', a: at(at(v('k'))), b: c(1)}, 'k')).toBe(true)
  expect(plainKey({op: '<=', a: at({op: 'add', a: v('k'), b: c(1)}), b: c(1)}, 'k')).toBe(false)
  expect(plainKey({op: '<', a: v('k'), b: v('a')}, 'k')).toBe(false)
})

test('a write at every key with its key in key terms: every cell as brute force computes it', () => {
  for (let trial = 0; trial < 300; trial++) {
    const val = value(2)
    const m: Machine = {name: 'keys', params: [], inputs: ['a', 'b'], state: {}, maps: {M: 0}, inputMaps: ['I', 'J'], step: {maps: {M: {each: 'k', value: val}}}}
    const run = interpret(m), gen = loadJs(m)
    const env = {a: rand(6), b: rand(6)}, I = randomMap(), J = randomMap(), input = {...env, I, J}
    const st = run.step({}, run.init({}), input), g = gen.step({}, gen.init({}), input)
    const read = (s: typeof st, k: number) => s.maps.M!.get(k) ?? s.defaults?.M ?? 0
    for (let k = 0; k <= 400; k++) {
      const want = evalBrute(val, k, env, I, J)
      expect(read(st, k), JSON.stringify({val, env, I: [...I], J: [...J], k})).toBe(want)
      expect(read(g, k)).toBe(want)
    }
  }
})
