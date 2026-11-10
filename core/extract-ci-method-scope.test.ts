import {expect, test} from 'bun:test'
import {extract} from './extract.ts'
import {buildLaw} from './laws.ts'

// Lane D's method-scope probe, with scalar/input and inference controls.
const x = extract('export class C { first(){return {value:7,failed:true}} second(){return {other:9}} }', {entry: 'C', check: {runs: 0, states: 0, probes: false}})
expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
for (const field of ['value', 'failed']) test(`qualified ${field} cannot rebind a law to another method`, () => {
  const expr = `result.${field} == ${field === 'value' ? '7' : 'true'}`
  const own = buildLaw(x, {name: 'matching method', expr, method: 'first'})
  expect(own.kind).toBe('step')
  if (own.kind === 'step') expect(own.method).toBe('first')
  expect(() => buildLaw(x, {name: 'method boundary', expr, method: 'second'})).toThrow('bound to second')
  const inferred = buildLaw(x, {name: 'infer unique owner', expr})
  expect(inferred.kind).toBe('step')
  if (inferred.kind === 'step') expect(inferred.method).toBe('first')
})
test('explicit method also governs scalar results and arguments', () => {
  const y = extract('export class C { first(a:number){return a} second(){return {other:9}} }', {entry: 'C', check: {runs: 0, states: 0, probes: false}})
  expect(y.ok).toBe(true)
  for (const expr of ['result == 7', 'a == 7', 'first.a == 7']) expect(() => buildLaw(y, {name: expr, expr, method: 'second'})).toThrow('bound to second')
  const own = buildLaw(y, {name: 'same method', expr: 'result == a', method: 'first'})
  expect(own.kind).toBe('step')
  if (own.kind === 'step') expect(own.method).toBe('first')
})
