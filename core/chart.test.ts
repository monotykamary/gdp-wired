// Statecharts (core/chart.ts): the examples proven and their broken variants caught, every reach run replayed on the
// compiled rule, a state no run reaches proven so, nesting, history and parallel regions against a hand-written
// reference, and what a chart refuses to build.
import {expect, test} from 'bun:test'
import {chart} from './chart.ts'
import {order, orderLaws, checkout, checkoutLaws} from '../examples/charts.ts'

test('the order chart: every state reached by a run the compiled rule takes, its laws proven, its broken variants caught', () => {
  const o = order(), report = o.check({params: {tries: 2}})
  expect(report).toMatchObject({ok: true, stuck: [], ambiguous: []})
  // each reach run, replayed on the compiled rule, ends in its state
  const g = o.rule.compiled(), ps = o.rule.encodeParams({tries: 2} as never)
  for (const [state, how] of Object.entries(report.reached)) {
    if (typeof how === 'string') throw new Error(`${state} is ${how}`)
    let st = g.init(ps)
    for (const req of how.run) st = g.step(ps, st, o.rule.encodeInput(req as never))
    expect(o.rule.decode(st).state).toBe(state)
  }
  const {laws, stepLaws} = orderLaws(o)
  expect(o.prove(laws, stepLaws)).toMatchObject({proven: true, checked: true})
  const r = order('refunds a shipped order'), v = r.prove(orderLaws(r).laws, orderLaws(r).stepLaws)
  expect(v.proven).toBe(false)
  expect(v.run?.trace.length).toBeGreaterThan(0)
  expect(order('ships two ways').check({params: {tries: 2}}).ambiguous.map(a => a.event)).toEqual(['ship'])
  expect(order('a state with no way out').check({params: {tries: 2}}).stuck).toEqual(['lost'])
})

test('parallel regions react to the same event, and a guard reads another region', () => {
  const k = checkout()
  expect(k.check()).toMatchObject({ok: true, stuck: [], ambiguous: []})
  expect(k.prove(checkoutLaws(k))).toMatchObject({proven: true, checked: true})
  expect(checkout('ships unpaid').prove(checkoutLaws(checkout('ships unpaid'))).proven).toBe(false)
  // one event moves two regions at once
  const both = chart('both').regions({a: {states: {x: {}, y: {final: true}}}, b: {states: {x: {}, y: {final: true}}}}).on('go', {from: 'a.x', to: 'a.y'}).on('go', {from: 'b.x', to: 'b.y'})
  const g = both.rule.compiled(), st = g.step({}, g.init({}), both.rule.encodeInput({event: 'go'} as never))
  expect(both.rule.decode(st)).toEqual({a: 'y', b: 'y'})
})

test('a state no run reaches is proven unreachable, and nesting, history and context run as a statechart does', () => {
  const c = chart('door').context({opened: 0}).states({
    closed: {}, open: {states: {ajar: {}, wide: {}}, history: true}, locked: {}, gone: {final: true},
  })
    .on('open', {from: 'closed', to: 'open', set: ({opened}) => ({opened: opened.plus(1)})})
    .on('widen', {from: 'open.ajar', to: 'open.wide'})
    .on('close', {from: 'open', to: 'closed'})
    .on('lock', {from: 'closed', to: 'locked', when: env => env.in('locked')}) // needs to be locked already: never taken
    .on('leave', {from: ['closed', 'locked'], to: 'gone'})
  const report = c.check()
  expect(report.reached.locked).toBe('unreachable')
  expect(report.ok).toBe(true)
  // against a reference: open enters ajar, then wherever it was last; close from either child; the count of openings
  const g = c.rule.compiled()
  let st = g.init({}), ref = {state: 'closed', last: 'open.ajar', opened: 0}
  const step = (event: string) => {
    st = g.step({}, st, c.rule.encodeInput({event} as never))
    if (event === 'open' && ref.state === 'closed') ref = {...ref, state: ref.last, opened: ref.opened + 1}
    else if (event === 'widen' && ref.state === 'open.ajar') ref = {...ref, state: 'open.wide', last: 'open.wide'}
    else if (event === 'close' && ref.state.startsWith('open')) ref = {...ref, state: 'closed'}
    else if (event === 'leave' && (ref.state === 'closed' || ref.state === 'locked')) ref = {...ref, state: 'gone'}
    const got = c.rule.decode(st) as Record<string, unknown>
    expect({state: got.state, last: got['state.last.open'], opened: got.opened}).toEqual(ref)
  }
  for (const e of ['widen', 'open', 'widen', 'close', 'open', 'close', 'lock', 'open', 'close', 'leave', 'open']) step(e)
  expect(c.law('opened at least once when open', env => env.in('open').implies(env.opened.atLeast(1)))).toBeDefined()
  expect(c.prove([c.law('opened at least once when open', env => env.in('open').implies(env.opened.atLeast(1)))])).toMatchObject({proven: true, checked: true})
})

test('a chart that names no such state, a bad initial state or a cross-region transition is refused when built', () => {
  expect(() => chart('a').states({x: {}}).on('go', {from: 'x', to: 'y'}).rule).toThrow(/no state y/)
  expect(() => chart('a').states({x: {states: {p: {}}, initial: 'q'}}).on('go', {from: 'x', to: 'x'}).rule).toThrow(/initial state q/)
  expect(() => chart('a').regions({r: {states: {x: {}}}, s: {states: {y: {}}}}).on('go', {from: 'r.x', to: 's.y'}).rule).toThrow(/one region to another/)
  expect(() => chart('a').states({x: {}}).on('go', {from: 'x', to: 'x'}).last({}, 'x')).toThrow(/keeps no history/)
})
