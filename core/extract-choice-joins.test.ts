import {expect, test} from 'bun:test'
import {extract} from './extract.ts'

const options = {entry: 'decide', mode: 'standalone' as const, check: {runs: 0, states: 0, probes: false as const}}

test('different ordered choice domains cannot be silently joined or assigned', () => {
  for (const body of [
    'const c = pick ? a : b; return c === b;',
  ]) {
    const x = extract(`export function decide(pick: boolean, a: 'red' | 'blue', b: 'red' | 'green'): boolean { ${body} }`, options)
    expect(x.ok).toBe(false)
    expect(x.refusals.map(r => r.what).join(' ')).toContain('different ordered choice domains')
  }
})

test('same-domain joins preserve every choice with source replay disabled', () => {
  const x = extract("export function decide(pick: boolean, a: 'red' | 'blue', b: 'red' | 'blue'): boolean { const c = pick ? a : b; return c === b; }", options)
  expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
  const rule = x.rule!, run = rule.interpreter(), p = rule.encodeParams({}), output = x.model!.results!.decide!
  if (output.k !== 'maybe') throw new Error('expected result layout')
  for (const pick of [false, true]) for (const a of ['red', 'blue']) for (const b of ['red', 'blue']) {
    const decoded = rule.decode(run.step(p, run.init(p), rule.encodeInput({pick, a, b})))
    expect(decoded[output.name]).toBe((pick ? a : b) === b)
    expect(decoded[output.missing]).toBe(false)
  }
})
