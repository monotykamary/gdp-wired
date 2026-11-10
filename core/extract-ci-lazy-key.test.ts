import {expect, test} from 'bun:test'
import {extract} from './extract.ts'
import {type Sort, lazyKey, sameLazyRoot} from './extract-read.ts'

function expectChoice(sort: Sort, literal: string) {
  // An asymmetric toMatchObject matcher can replace the inspected nested array in Bun.
  expect(sort.k).toBe('choice')
  if (sort.k !== 'choice') throw new Error('expected choice')
  expect(new Set(sort.values)).toEqual(new Set([literal, '@@other']))
}

// Lane D's paired controls: all six were accepted before the prefix-only repair.
for (const field of ['safe_value', 'arg1_value']) for (const [label, expr] of [
  ['numbers', `a.${field} === b.value`],
  ['numeric-choice', `a.${field} === 7 && b.value === 'red'`],
  ['choice-choice', `a.${field} === 'blue' || b.value === 'red'`],
] as const) test(`P2 structured lazy keys: ${field}/${label}`, () => {
  const x = extract(`export function decide(state: number = 0, a, b): number { return (${expr}) ? state + 1 : state }`, {entry: 'decide'})
  expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
  expect(x.evidence!.requests).toBeGreaterThan(0)
  const inputs = x.model!.inputs.filter(v => v.name !== x.model!.event)
  expect(inputs).toHaveLength(2)
  expect(new Set(inputs.map(v => v.name)).size).toBe(2)
  if (label === 'numeric-choice') {
    expect(inputs[0]!.sort.k).toBe('num')
    expectChoice(inputs[1]!.sort, 'red')
  }
  if (label === 'choice-choice') {
    expectChoice(inputs[0]!.sort, 'blue')
    expectChoice(inputs[1]!.sort, 'red')
  }
  if (label !== 'numbers') {
    // A required field has the named literal and an other-string case, not an absent case.
    expect(x.model!.events).toHaveLength(2)
    const discriminant = inputs[1]!.sort
    if (discriminant.k !== 'choice') throw new Error('expected second argument choice')
    expect(new Set(x.model!.events.map(event => event.select[inputs[1]!.name]))).toEqual(new Set(discriminant.values))
    for (const event of x.model!.events) {
      expect(Object.keys(event.select)).toEqual([inputs[1]!.name])
      const sort = inputs[1]!.sort
      if (sort.k !== 'choice') throw new Error('expected second argument choice')
      expect(sort.values).toContain(event.select[inputs[1]!.name]!)
    }
  }
})

test('P2 structured lazy keys separate identity from readable names', () => {
  const first = {prefix: '', root: ['', 0] as const}, second = {prefix: 'arg1_', root: ['', 1] as const}
  expect(lazyKey(first, 'arg1_value')).not.toBe(lazyKey(second, 'value'))
  expect(sameLazyRoot(first, second)).toBe(false)
  expect(lazyKey({...first, prefix: 'another_name_'}, 'value')).toBe(lazyKey(first, 'value'))
  expect(sameLazyRoot({...first, prefix: 'another_name_'}, first)).toBe(true)
  expect(lazyKey({prefix: 'a', root: ['a', 1]}, 'b_c')).not.toBe(lazyKey({prefix: 'a_b', root: ['a_b', 1]}, 'c'))
})

test('P2 structured lazy keys retain retyping independently of a colliding choice', () => {
  const x = extract(`export function decide(state: string = '', a, b): string { if (b.value === 'red') return a.arg1_value; return state }`, {entry: 'decide'})
  expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
  const inputs = x.model!.inputs.filter(v => v.name !== x.model!.event)
  expect(inputs).toHaveLength(2)
  expect(inputs.find(v => x.model!.lazy!.get(v.name)?.field === 'arg1_value')!.sort.k).toBe('str')
  expectChoice(inputs.find(v => x.model!.lazy!.get(v.name)?.field === 'value')!.sort, 'red')
  expect(x.evidence!.requests).toBeGreaterThan(0)
})

test('P2 structured lazy keys still intern repeated reads of the same field', () => {
  const x = extract(`export function decide(state: number = 0, a, b): number { return a.value === a.value && b.value !== 7 ? state + 1 : state }`, {entry: 'decide'})
  expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
  expect(x.model!.inputs.filter(v => v.name !== x.model!.event)).toHaveLength(2)
  expect(x.model!.lazy!.size).toBe(2)
  expect(x.evidence!.requests).toBeGreaterThan(0)
})
