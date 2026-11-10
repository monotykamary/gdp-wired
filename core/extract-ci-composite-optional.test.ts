import {expect, test} from 'bun:test'
import {extract} from './extract.ts'
import {buildLaw} from './laws.ts'
import {proveSteps} from './dsl.ts'

const x = extract('export class C { m=new Map<string,number>(); decide(k:string):number|undefined{return this.m.get(k)} }', {entry: 'C'})
expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
const opts = {clock: 1, calendar: {weekend: ['sat', 'sun']}}
for (const [id, expr] of Object.entries({direct: 'result - 0 <= 1 business days', nested: '(result + 0) - 0 <= 1 business days', negated: '(-result) - 0 <= 1 business days', minimum: 'min(result, 0) - 0 <= 1 business days', absolute: 'abs(result) - 0 <= 1 business days', maximum: '0 - max(0, result) <= 1 business days', product: '(2 * result) - 0 <= 1 business days', division: '(result // 2) - 0 <= 1 business days'})) test(`B1 ${id}: calendar operands retain optional provenance`, () => {
  expect(() => buildLaw(x, {name: id, expr, method: 'decide'}, opts)).toThrow('optional')
})
test('nonoptional class and standalone calendar laws remain proven', () => {
  for (const [source, expr, standalone] of [
    ['export class C { decide():number {return 0} }', 'result - 0 <= 1 business days', false],
    ['export class C { decide():number {return 0} }', '1 business days >= (result + 0) - 0', false],
    ['export function decide(n:0):boolean{return true}', '(n + 0) - 0 <= 1 business days', true],
  ] as const) {
    const y = extract(source, standalone ? {entry: 'decide', mode: 'standalone'} : {entry: 'C'})
    expect(y.ok).toBe(true)
    const b = buildLaw(y, {name: expr, expr, method: 'decide'}, opts)
    if (b.kind !== 'step') throw Error('expected a step law')
    expect(proveSteps(y.rule!, y.invariants ?? [], [b.law], {from: 'any', search: false})).toMatchObject({proven: true, checked: true})
  }
})
