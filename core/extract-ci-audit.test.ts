import {expect, test} from 'bun:test'
import {extract} from './extract.ts'
import {buildLaw} from './laws.ts'

test('CI audit B1: default replay cannot validate optional calendar law translation', () => {
  for (const absent of ['undefined', 'null']) for (const standalone of [true, false]) {
    const method = `decide(flag: boolean): number | ${absent} { if (flag) return 0; return ${absent}; }`
    const source = standalone ? `export function ${method}` : `export class Decision { ${method} }`
    const x = extract(source, standalone ? {entry: 'decide', mode: 'standalone'} : {entry: 'Decision'})
    expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
    expect(x.evidence!.requests).toBeGreaterThan(0)
    expect(x.evidence!.fromStates).toBeGreaterThan(0)
    for (const expr of ['result - 0 <= 1 business days', '1 business days >= result - 0', '0 - result <= 1 business days']) {
      expect(() => buildLaw(x, {name: expr, expr, method: 'decide'}, {clock: 1, calendar: {weekend: ['sat', 'sun']}})).toThrow('arithmetic on an optional')
    }
  }
})
