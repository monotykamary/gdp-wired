import {expect, test} from 'bun:test'
import {extract} from './extract.ts'
import {buildLaw} from './laws.ts'

test('CI audit B1: default replay cannot validate optional calendar law translation', () => {
  for (const [source, standalone] of [
    ['export function decide(flag: boolean): number | undefined { if (flag) return 0; }', true],
    ['export function decide(flag: boolean): number | null { return flag ? 0 : null; }', true],
    ['export class Decision { values = new Map<string, number>(); decide(key: string): number | undefined { return this.values.get(key); } }', false],
  ] as const) {
    const x = extract(source, standalone ? {entry: 'decide', mode: 'standalone'} : {entry: 'Decision'})
    expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
    expect(x.evidence!.requests).toBeGreaterThan(0)
    expect(x.evidence!.fromStates).toBeGreaterThan(0)
    for (const expr of ['result - 0 <= 1 business days', '1 business days >= result - 0', '0 - result <= 1 business days']) {
      expect(() => buildLaw(x, {name: expr, expr, method: 'decide'}, {clock: 1, calendar: {weekend: ['sat', 'sun']}})).toThrow('arithmetic on an optional')
    }
  }
})
