import {expect, test} from 'bun:test'
import {type Law, type Machine, all, get, n, same, x} from './machine.ts'
import {certFor} from './counts.ts'
import {proveFixedCountPhase} from './count-phase.ts'
import {proveFixedCountFrame} from './count-fixed-frame.ts'
import {checkMC, countedObligations} from '../kernel/kernel.ts'
import {clock, counted, fullRate, withWall} from '../kernel/prove.ts'
function fixture(prefix: string) {
  const name = (suffix: string) => prefix + suffix, at = (a: string, b: string) => ({op: 'add' as const, a: {op: 'mul' as const, k: 4, a: x(a)}, b: x(b)})
  const member = same(get(name('rows'), at('r', 'k')), n(1)), below = x('size')
  const m: Machine = {name: 'renamed phase fixture', params: ['size'], inputs: ['op'], pre: all({op: '<=', a: n(1), b: below}, {op: '<=', a: below, b: n(4)}), assume: all(same(x('op'), n(0)), {op: 'or', xs: [0, 1, 2].map(i => same(x('op'), n(i)))}), state: {[name('phase')]: n(0)}, maps: {[name('rows')]: 0, [name('tick')]: 0, [name('limit')]: 0}, step: {}, counts: {
    [name('voters')]: {j: 'r', lo: 'q', key: 'k', base: 4, below, body: {op: 'if', c: all(member, {op: '<', a: get(name('tick'), x('k')), b: get(name('limit'), x('q'))}), then: n(1), else: n(0)}},
    [name('size')]: {j: 'r', key: 'k', below, body: {op: 'if', c: member, then: n(1), else: n(0)}}
  }}
  const law: Law = {name: 'majority bound', forall: 'a', keys: ['b'], holds: {op: 'or', xs: [{op: 'not', x: all({op: '<', a: x('a'), b: below}, {op: '<', a: x('b'), b: below})}, {op: '<=', a: {op: 'mul', k: 2, a: get(name('voters'), at('a', 'b'))}, b: get(name('size'), x('a'))}]}}
  const premise: Law = {name: 'existing phase premise', forall: 't', holds: {op: 'or', xs: [{op: 'not', x: same(x(name('phase')), n(0))}, same(get(name('limit'), x('t')), n(0))]}}
  return {m, law, family: [law, premise], name}
}
const request = (g: Parameters<typeof certFor>[0], ds: Parameters<typeof certFor>[1]) => certFor(g, ds, false, 0, () => true)
test('phase strategy returns checked INIT and STEP without mutating seeds', () => {
  const {m, law, family} = fixture('arbitrary_'), seed = {}, before = JSON.stringify([m, family, seed]), trace: string[] = []
  const result = counted(fullRate, () => withWall(performance.now() + 2000, () => proveFixedCountPhase(m, family, law, seed, clock() + 2000, request, stage => trace.push(stage))))
  if (!result) throw Error('phase strategy stopped: ' + trace.join(', '))
  expect(result).toBeDefined(); expect(JSON.stringify([m, family, seed])).toBe(before)
  for (const p of countedObligations(m, family, {[law.name]: result.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, result.certs[p.goal.name]!)).toBe(true)
  const frames = Object.values(result.certs).flatMap(c => c.frames ?? [])
  expect(frames).toHaveLength(2); expect(frames.every(f => !f.when.length)).toBe(true)
})
test('composition-only phase proposals omit INIT and are not standalone proofs', () => {
  const {m, law, family} = fixture('proposal_'), events: string[] = []
  const result = counted(fullRate, () => withWall(performance.now() + 2000, () => proveFixedCountPhase(m, family, law, {}, clock() + 2000, request, stage => events.push(stage), {deferToComposition: true})))
  expect(result).toBeDefined()
  expect(events).toContain('proposed-step')
  expect(events).not.toContain('checked-step')
  expect(result?.certs[law.name + ' @start']).toBeUndefined()
  expect(result?.certs[law.name + ' @step']).toBeDefined()
})
test('a threshold update that can violate the count bound is not proved', () => {
  const {m, law, family, name} = fixture('broken_')
  m.step.maps = {[name('limit')]: {each: 'changedKey', value: n(1)}}
  const result = counted(fullRate, () => withWall(performance.now() + 1000, () => proveFixedCountPhase(m, family, law, {}, clock() + 500, request)))
  expect(result).toBeUndefined()
})

test('unchanged target counts need no phase premise', () => {
  const {m, law} = fixture('frame_'), family = [law], seed = {}, before = JSON.stringify([m, seed])
  const result = counted(fullRate, () => withWall(performance.now() + 2000, () => proveFixedCountFrame(m, family, law, seed, clock() + 2000, request)))
  expect(result).toBeDefined(); expect(JSON.stringify([m, seed])).toBe(before)
  if (result) for (const p of countedObligations(m, family, {[law.name]: result.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, result.certs[p.goal.name]!)).toBe(true)
})
test('minimal-view-first frame and phase proposals still check on original obligations', () => {
  const {m, law, family} = fixture('minimal_')
  const result = counted(fullRate, () => withWall(performance.now() + 2000, () => proveFixedCountPhase(m, family, law, {}, clock() + 2000, request, undefined, {minimalView: true})))
  expect(result).toBeDefined()
  if (result) for (const p of countedObligations(m, family, {[law.name]: result.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, result.certs[p.goal.name]!)).toBe(true)
})

test('expired phase strategy does not build a count request', () => {
  const {m, law, family} = fixture('expired_'); let called = false
  expect(proveFixedCountPhase(m, family, law, {}, clock() - 1, (g, ds) => {called = true; return request(g, ds)})).toBeUndefined()
  expect(called).toBe(false)
})
test('an unbounded operation choice is not silently treated as fixed', () => {
  const {m, law, family} = fixture('unfixed_'); delete m.assume
  expect(proveFixedCountPhase(m, family, law, {}, clock() + 100, request)).toBeUndefined()
})
