import {expect, test} from 'bun:test'
import {extract} from './extract.ts'
import {buildLaw} from './laws.ts'
import {proveSteps} from './dsl.ts'

const read = (source: string) => {
  // Deliberately no replay or prover probes: the extracted model itself must be sound.
  const x = extract(source, {entry: 'decide', mode: 'standalone', check: {runs: 0, states: 0, probes: false}})
  expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
  return x
}

test('absence narrowing distinguishes strict/loose null and undefined and preserves the absent tag', () => {
  for (const absence of ['undefined', 'null'] as const) for (const literal of ['undefined', 'null'] as const) for (const op of ['===', '!==', '==', '!='] as const) {
    const x = read(`export function decide(flag: boolean, missing: boolean): boolean {
      const value = missing ? ${absence} : flag;
      if (value ${op} ${literal}) return value === ${absence};
      return value !== ${absence};
    }`)
    const r = x.rule!, run = r.interpreter(), params = r.encodeParams({}), out = x.model!.results!.decide!
    if (out.k !== 'maybe') throw new Error('expected result layout')
    const absent = absence === 'null' ? null : undefined, compared = literal === 'null' ? null : undefined
    for (const value of [absent, false, true]) for (const unused of [false, true]) {
      const equal = op === '==' || op === '!=' ? value === null || value === undefined : value === compared
      const condition = op.startsWith('!') ? !equal : equal
      const wanted = condition ? value === absent : value !== absent
      const state = run.step(params, run.init(params), r.encodeInput({flag: value ?? unused, missing: value === absent}))
      expect(r.decode(state)[out.missing]).toBe(false)
      expect(r.decode(state)[out.name], `${absence} ${op} ${literal}, input ${String(value)}`).toBe(wanted)
    }
  }
}, 60000)

test('strict comparison to a different absence kind cannot prove a false decision law', () => {
  const x = read('export function decide(flag: boolean | undefined): boolean { if (flag !== null) return flag === undefined; return false; }')
  const built = buildLaw(x, {name: 'false claim', expr: 'result == false', method: 'decide'})
  if (built.kind !== 'step') throw new Error('expected step law')
  expect(proveSteps(x.rule!, x.invariants ?? [], [built.law], {from: 'any', search: false}).proven).toBe(false)
})
