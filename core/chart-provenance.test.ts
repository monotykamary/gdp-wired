import {expect, test} from 'bun:test'
import {chart} from './chart.ts'
import {nat, proveRule, rule} from './dsl.ts'

test('reserved characters in nested chart history labels are stored safely and their laws are checked', () => {
  const c = chart('history labels').states({
    outer: {states: {'foo?': {history: true, states: {a: {}, b: {}}}}}, outside: {},
  })
    .on('advance', {from: 'outer.foo?.a', to: 'outer.foo?.b'})
    .on('leave', {from: 'outer', to: 'outside'})
    .on('return', {from: 'outside', to: 'outer.foo?'})
  const r = c.rule, keys = Object.keys(r.machine.state)
  const history = keys.find(k => k.startsWith('gdp$chart$history$'))!
  expect(history).toBeDefined()
  expect(keys).not.toContain('state.last.outer.foo?')
  const law = c.law('history remembers a child', e => e.last('outer.foo?').is('outer.foo?.a').or(e.last('outer.foo?').is('outer.foo?.b')))
  expect(JSON.stringify(law.holds)).toContain(history)
  expect(proveRule(r, [law], {search: false})).toMatchObject({proven: true, checked: true})
  expect(c.prove([law], [], {search: false})).toMatchObject({proven: true, checked: true})
  const g = r.compiled()
  let st = g.init({})
  for (const event of ['advance', 'leave', 'return']) st = g.step({}, st, r.encodeInput({event} as never))
  expect(r.decode(st).state).toBe('outer.foo?.b')
})

test('history fields neither shadow user fields nor change ordinary legacy names', () => {
  const fallback = 'gdp$chart$history$00730074006100740065$0066006f006f003f'
  const c = chart('collisions').context({'state.last.safe': 7, [fallback]: 8}).outputs({'state.last.output': 3}).states({
    safe: {history: true, states: {a: {}, b: {}}},
    'foo?': {history: true, states: {a: {}, b: {}}},
    ordinary: {history: true, states: {a: {}, b: {}}},
    output: {history: true, states: {a: {}, b: {}}},
  }).on('go', {from: 'safe.a', to: 'safe.b'})
  const r = c.rule, decoded = r.decode(r.compiled().init({})) as Record<string, unknown>
  expect(decoded['state.last.safe']).toBe(7)
  expect(decoded[fallback]).toBe(8)
  expect(decoded['state.last.ordinary']).toBe('ordinary.a')
  expect(decoded['state.last.output']).toBe(3)
  expect(decoded[`${fallback}$1`]).toBe('foo?.a')
  expect(Object.keys(decoded).filter(k => k.startsWith('gdp$chart$history$'))).toHaveLength(4)
  expect(c.prove([], [], {search: false})).toMatchObject({proven: true, checked: true})
})

test('user rule declarations cannot forge reserved generated identities', () => {
  for (const name of ['?step0:x', 'state.last.foo?', 'x#y', "x'y"]) {
    expect(() => rule('forged').state({[name]: 0}).machine).toThrow(/reserved/)
    expect(() => rule('forged').params({[name]: nat}).machine).toThrow(/reserved/)
  }
})
