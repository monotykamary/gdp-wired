import {expect, test} from 'bun:test'
import {evalC, interpret, loadJs, type E, type Machine} from '../core/machine.ts'
import {checkLaws, obligations, scope} from './kernel.ts'
import {proveLaws} from './prove.ts'
import {wordDivisionName, parseWordDivisionName, wordDivisionKey, wordDivisionValue, wordDivisionFacts} from './word-division.ts'
const widths = [8, 16, 32, 64] as const
const m: Machine = {name: 'internal total unsigned division helper', params: [], inputs: [], state: {}, step: {}}
const st = {scalars: {}, maps: {}}
const constant = (value: number): E => ({op: 'const', value})
function exercise(width: typeof widths[number], a: bigint, b: bigint): void {
  const n = width === 8 ? 1 : width / 16, base = width === 8 ? 256n : 65536n
  const digit = (x: bigint) => Array.from({length: n}, (_, i) => Number(x / (base ** BigInt(i)) % base))
  const values = [...digit(a), ...digit(b)], names = values.map((_, i) => `x${i}`)
  const key = wordDivisionKey(names.map(name => ({op: 'var', name})))
  const get: E = {op: 'get', map: wordDivisionName(width, 'q', 0), key}
  const env = Object.fromEntries(names.map((name, i) => [name, values[i]!]))
  for (const c of wordDivisionFacts([get])) expect(evalC(c, env, st, m)).toBe(true)
  const q = b === 0n ? 0n : a / b, r = b === 0n ? 0n : a % b
  for (let i = 0; i < n; i++) {
    expect(wordDivisionValue(width, 'q', i, values)).toBe(Number(q / (base ** BigInt(i)) % base))
    expect(wordDivisionValue(width, 'r', i, values)).toBe(Number(r / (base ** BigInt(i)) % base))
  }
}

test('compact division samples and guarded theory match exact arithmetic at every width', () => {
  let seed = 17n
  for (const width of widths) {
    const max = (1n << BigInt(width)) - 1n
    for (const a of [0n, 1n, max, max - 1n, max / 2n]) for (const b of [0n, 1n, 2n, 3n, max, max / 2n]) exercise(width, a, b)
    for (let i = 0; i < 48; i++) {
      seed = (seed * 6364136223846793005n + 1n) & ((1n << 64n) - 1n); const a = seed & max
      seed = (seed * 6364136223846793005n + 1n) & ((1n << 64n) - 1n); exercise(width, a, seed & max)
    }
  }
})

test('compact division invalid and out-of-domain inputs cannot activate unguarded equations', () => {
  for (const width of widths) {
    const n = width === 8 ? 1 : width / 16, base = width === 8 ? 256 : 65536
    const names = Array.from({length: 2 * n}, (_, i) => `x${i}`), key = wordDivisionKey(names.map(name => ({op: 'var', name})))
    const get: E = {op: 'get', map: wordDivisionName(width, 'q', 0), key}
    for (const first of [base, base + 1, Number.MAX_SAFE_INTEGER]) {
      const values = Array.from({length: 2 * n}, () => 0); values[0] = first; values[n] = 1
      const env = Object.fromEntries(names.map((name, i) => [name, values[i]!]))
      for (const c of wordDivisionFacts([get])) expect(evalC(c, env, st, m)).toBe(true)
    }
  }
  for (const bad of [-1, 0.5, NaN, Infinity, Number.MAX_SAFE_INTEGER + 1])
    expect(() => wordDivisionValue(8, 'q', 0, [bad, 1])).toThrow()
})

test('compact division parser and scope reject malformed names, arities and declaration aliases', () => {
  for (const bad of ['worddiv$9$q$0', 'worddiv$64$q$4', 'worddiv$8$c$0', 'worddiv$8$q$00', 'worddiv$8$q$-1']) expect(parseWordDivisionName(bad)).toBeUndefined()
  const name = wordDivisionName(8, 'q', 0)
  for (const variant of [{maps: {[name]: 0}}, {inputMaps: [name]}, {fns: {[name]: {js: '() => 0'}}}])
    expect(() => scope({...m, ...variant})).toThrow('reserved')
  expect(() => scope({...m, state: {q: constant(0)}, step: {state: {q: {op: 'get', map: name, key: constant(0)}}}})).toThrow('tuple')
  const machine: Machine = {...m, inputs: ['a', 'b'], state: {q: constant(0)}, step: {state: {q: {op: 'get', map: name, key: wordDivisionKey([{op: 'var', name: 'a'}, {op: 'var', name: 'b'}])}}}}
  for (const engine of [interpret(machine), loadJs(machine)]) expect(engine.step({}, engine.init({}), {a: 255, b: 3}).scalars.q).toBe(85)
})

test('compact division samples preserve strict normalized bounds with a checked certificate', () => {
  const machine: Machine = {...m, inputs: ['a', 'b'], state: {q: constant(0)}, step: {state: {q: {op: 'get', map: wordDivisionName(8, 'q', 0), key: wordDivisionKey([{op: 'var', name: 'a'}, {op: 'var', name: 'b'}])}}}}
  const law = {name: 'normalized quotient bound', holds: {op: '<' as const, a: {op: 'var' as const, name: 'q'}, b: constant(256)}}
  const report = proveLaws(machine, [law])
  expect(report.proven).toBe(true); expect(report.checked).toBe(true)
  expect(report.proof).toBeDefined()
  expect(checkLaws(machine, [law], report.proof!)).toBe(true)
  const bad = {...law, holds: {...law.holds, b: constant(1)}}
  expect(checkLaws(machine, [bad], report.proof!)).toBe(false)
  expect(proveLaws(machine, [bad]).proven).toBe(false)
})

test('compact division bounds at all widths keep the conclusion last and kernel-check', () => {
  for (const width of widths) {
    const n = width === 8 ? 1 : width / 16, base = width === 8 ? 256 : 65536
    const inputs = Array.from({length: 2 * n}, (_, i) => `x${i}`)
    const key = wordDivisionKey(inputs.map(name => ({op: 'var', name})))
    const machine: Machine = {...m, inputs, state: {q: constant(0)}, step: {state: {q: {op: 'get', map: wordDivisionName(width, 'q', 0), key}}}}
    const law = {name: 'all width quotient bound', holds: {op: '<' as const, a: {op: 'var' as const, name: 'q'}, b: constant(base)}}
    for (const goal of obligations(machine, [law])) expect(goal.hyps.at(-1)?.op).toBe('not')
    const report = proveLaws(machine, [law])
    expect(report.proven).toBe(true); expect(report.checked).toBe(true)
    expect(checkLaws(machine, [law], report.proof!)).toBe(true)
  }
}, 30_000)

test('compact division exhaustive u8 theory has zero false equations', () => {
  const key = wordDivisionKey([{op: 'var', name: 'a'}, {op: 'var', name: 'b'}])
  const clauses = wordDivisionFacts([{op: 'get', map: wordDivisionName(8, 'q', 0), key}])
  for (let a = 0; a < 256; a++) for (let b = 0; b < 256; b++)
    for (const c of clauses) if (!evalC(c, {a, b}, st, m)) throw new Error(`false u8 theory at ${a}/${b}`)
  expect(clauses.length).toBeGreaterThan(0)
}, 180_000)
