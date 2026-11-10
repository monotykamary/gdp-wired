import {expect, test} from 'bun:test'
import {extract} from './extract.ts'

for (const typed of [true, false]) test(`P2 ${typed ? 'typed' : 'lazy'} records have independent scalar identities`, () => {
  const args = typed ? 'a:{value:number},b:{value:number}' : 'a,b'
  const source = `export class C {decide(${args}):boolean{return a.value===a.value && a.value===b.value}}`
  const x = extract(source, {entry: 'C', check: {runs: 0, states: 0, probes: false}})
  expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
  const m = x.model!, inputs = m.inputs.filter(v => v.name !== m.event)
  expect(inputs).toHaveLength(2)
  expect(new Set(inputs.map(v => v.name)).size).toBe(2)
  const r = x.rule!, interpreter = r.interpreter(), params = r.encodeParams({}), result = m.results!.decide!
  if (result.k !== 'scalar') throw Error('expected a scalar result')
  for (const a of [0, 1]) for (const b of [0, 1]) {
    const state = interpreter.step(params, interpreter.init(params), r.encodeInput({[m.event!]: 'decide', [inputs[0]!.name]: a, [inputs[1]!.name]: b}))
    expect(r.decode(state)[result.name]).toBe(a === b)
  }
  const replayed = extract(source, {entry: 'C'})
  expect({ok: replayed.ok, refusals: replayed.refusals}).toEqual({ok: true, refusals: []})
  expect(replayed.evidence!.requests).toBeGreaterThan(0)
})
test('repeated reads of one lazy argument still share a single scalar', () => {
  const x = extract('export class C {decide(a):boolean{return a.value===a.value}}', {entry: 'C'})
  expect(x.ok).toBe(true)
  expect(x.model!.inputs.filter(v => v.name !== x.model!.event)).toHaveLength(1)
})
