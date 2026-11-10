import {expect, test} from 'bun:test'
import {complexity, shrink} from './shrink.ts'
import {classify} from './classify.ts'
import {FAMILIES, Random, STRIDE, controls, evaluate, generate, inputs, lit, mix, native, nativeCheck, op, periodCertificate, render} from './model.ts'

test('translation fuzzer: source proofs and blocked model proofs remain distinct', () => {
  expect(classify({proven: true, checked: true}, false, true)).toBe('FINDING')
  expect(classify({kernelProven: true, translation: 'error'}, false, true)).toBe('BLOCKED_FINDING')
  expect(classify({kernelProven: true, translation: 'unchecked'}, false, false)).toBe('MODEL_FINDING')
  expect(classify({kernelProven: true, translation: 'error'}, true, true)).toBe('FALSE_REJECTION')
  expect(classify({proven: true, checked: true, translation: 'unchecked'}, true, true)).toBe('UNSAFE_VERDICT')
})

test('translation fuzzer: reproducible words including seed zero and full-period certificate', () => {
  const r = new Random(0)
  expect([r.raw(), r.raw(), r.raw(), r.raw()]).toEqual([2654435769, 1013904242, 3668340011, 2027808484])
  const c = periodCertificate()
  expect(c.period).toBe(4294967296n)
  expect(c.product).toBe(1n)
  expect(c.stride % 2n).toBe(1n)
  for (let bits = 1; bits <= 16; bits++) {
    const size = 2 ** bits, seen = new Set<number>(); let state = 0
    for (let i = 0; i < size; i++) { expect(seen.has(state)).toBe(false); seen.add(state); state = (state + STRIDE) % size }
    expect(state).toBe(0); expect(seen.size).toBe(size)
  }
  expect(new Set(Array.from({length: 10000}, (_, i) => mix(i))).size).toBe(10000)
})

test('translation fuzzer: random access generation, partitioning and mandatory coverage', () => {
  const all = Array.from({length: 4 * FAMILIES.length}, (_, i) => generate(17, i))
  expect(all).toEqual(Array.from({length: all.length}, (_, i) => generate(17, i)))
  expect(all).not.toEqual(Array.from({length: all.length}, (_, i) => generate(18, i)))
  const partitioned = Array.from({length: 7}, (_, shard) => all.filter((_, i) => i % 7 === shard)).flat()
  expect(new Set(partitioned.map(c => c.id)).size).toBe(all.length)
  expect(new Set(all.map(c => c.family)).size).toBe(FAMILIES.length)
  const tags = new Set(all.flatMap(c => c.tags))
  for (const tag of ['boolean', 'choice', 'number', 'optional', 'nullable', 'record', 'Map.get', 'early-return', 'truthiness', 'strict-null', 'calendar']) expect(tags.has(tag)).toBe(true)
  for (const c of all) {
    expect(inputs(c).length).toBeGreaterThan(0)
    const run = native(c)
    for (const row of inputs(c)) expect(() => run(row.args, row.entries)).not.toThrow()
    for (const law of c.laws) expect(typeof render(law, true)).toBe('string')
  }
})

test('translation fuzzer: shrink candidates terminate by strictly decreasing AST size', () => {
  for (let i = 0; i < 52; i++) for (const law of generate(31, i).laws) {
    for (const smaller of shrink(law)) expect(complexity(smaller)).toBeLessThan(complexity(law))
  }
})

test('translation fuzzer: independent oracle uses strict absence and native arithmetic', () => {
  expect(evaluate(op('==', {k: 'undefined'}, lit(null)), {})).toBe(false)
  expect(evaluate(op('>=', {k: 'undefined'}, lit(0)), {})).toBe(false)
  expect(evaluate({k: 'calendar', a: lit(0), b: {k: 'undefined'}, days: 1, op: '<='}, {})).toBe(false)
  expect(evaluate({k: 'calendar', a: lit(0), b: lit(86400), days: 1, op: '=='}, {})).toBe(true)
  expect(evaluate({k: 'calendar', a: lit(86400), b: lit(0), days: -1, op: '=='}, {})).toBe(true)
  for (const c of Object.values(controls())) expect(nativeCheck(c, c.laws[0]!).ok).toBe(false)
})
