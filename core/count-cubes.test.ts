import {expect, test} from 'bun:test'
import {type Machine, type Law, type State, all, any, atMost, get, ite, less, n, not, plus, same, times, x} from './machine.ts'
import {countCubes} from './count-cubes.ts'
import {finiteEvaluator, finiteHoudini} from './finite-houdini.ts'
import {finiteModelChecker} from './finite-model.ts'
import {boundaryState, lawFrontiers} from './finite-frontiers.ts'
import {holdsAt} from './exists.ts'
import {WallExpired} from './wall.ts'
import {withWall} from '../kernel/prove.ts'
const counter = (): Machine => ({name: 'counter', params: [], inputs: [], state: {value: n(0)}, step: {state: {value: plus(x('value'), n(1))}}})
const state = (value: number): State => ({scalars: {value}, maps: {}})
test('fresh one-key count cells extend the width-two cube vocabulary', () => {
  const source: Machine = {name: 'renamed rows', params: ['n'], inputs: ['i'], state: {ready: n(0)}, maps: {Rows: 0, Version: 0}, step: {state: {ready: get('Version', x('i'))}}}
  const m: Machine = {...source, counts: {sizeOfRow: {j: 'row', key: 'member', below: x('n'), body: ite(atMost(n(1), get('Rows', plus(times(8, x('row')), x('member')))), n(1), n(0))}}}
  const empty: State = {scalars: {ready: 0}, maps: {Rows: new Map(), Version: new Map()}}, full: State = {scalars: {ready: 1}, maps: {Rows: new Map([[0, 1], [8, 1]]), Version: new Map([[0, 1], [1, 1]])}}
  m.counts!.filtered = {...m.counts!.sizeOfRow!, body: ite(all(atMost(n(1), get('Rows', plus(times(8, x('row')), x('member')))), same(get('Version', x('row')), n(1))), n(1), n(0))}
  const laws = countCubes(source, m, [{p: {n: 2}, sts: [empty, full]}])
  expect(laws.every(l => !l.name.includes('filtered'))).toBe(true)
  const init = laws.find(l => l.name.includes('Version[x] is 0 and 1 <= sizeOfRow[x]'))!
  const twin = laws.find(l => l.name.includes('1 <= ready and sizeOfRow[x] is 0'))!
  expect(init).toBeDefined(); expect(twin).toBeDefined()
  expect(laws.every(l => [empty, full].every(st => holdsAt(m, l, {n: 2}, st, 4)))).toBe(true)
  const bad = {...empty, maps: {...empty.maps, Rows: new Map([[8, 1]])}}
  expect(holdsAt(m, init, {n: 2}, bad, 4)).toBe(false)
  expect(countCubes(source, source, [{p: {n: 2}, sts: [empty]}])).toEqual([])
  expect(countCubes(source, m, [{p: {n: 2}, sts: [empty, full]}], new Set())).toEqual([])
})
test('finite cover checks every explicit cell, not just small key numbers', () => {
  const m: Machine = {...counter(), maps: {A: 0}}, check = finiteEvaluator(m), law: Law = {name: 'zero', forall: 'i', holds: same(get('A', x('i')), n(0))}
  expect(check(law, {}, {...state(0), maps: {A: new Map([[100, 1]])}})).toBe(false)
  expect(check(law, {}, {...state(0), maps: {A: new Map([[100, 0]])}})).toBe(true)
  const unsupported = {...law, holds: same(get('A', times(2, x('i'))), n(0))}
  expect(check(unsupported, {}, {...state(0), maps: {A: new Map()}})).toBeUndefined()
})
test('finite cover derives auxiliary half-count bounds and preserves equality cases', () => {
  const m = counter(), check = finiteEvaluator(m)
  const law: Law = {name: 'half', forall: 'u', holds: any(not(all(atMost(times(2, x('u')), x('value')), less(x('value'), plus(times(2, x('u')), n(2))))), same(x('u'), n(5)))}
  expect(check(law, {}, state(10))).toBe(true)
  expect(check(law, {}, state(12))).toBe(false)
  expect(check({name: 'distinct fresh keys', forall: 'a', keys: ['b'], holds: same(x('a'), x('b'))}, {}, state(0))).toBe(false)
  expect(check({name: 'bounded equality alias', forall: 'a', keys: ['b'], holds: any(not(same(x('b'), n(100))), not(same(x('a'), x('b'))))}, {}, state(0))).toBe(false)
})
test('Houdini drops only post-violations from the current whole family, never callers', () => {
  const m = counter(), zero = {name: 'zero', holds: same(x('value'), n(0))}, caller = {name: 'caller zero', holds: same(x('value'), n(0))}, drops: string[] = []
  expect(finiteHoudini(m, m, [caller], [zero], [{p: {}, sts: [state(0)]}], {randomStates: 0, requests: 1, onDrop: d => drops.push(d.law.name)})).toEqual([])
  expect(drops).toEqual(['zero'])
  expect(finiteHoudini(m, m, [caller], [zero], [{p: {}, sts: [state(1)]}], {randomStates: 0, requests: 1})).toEqual([zero])
  const noProof: Law = {name: 'unsupported', forall: 'i', holds: same(times(2, x('i')), x('i'))}
  expect(finiteHoudini(m, m, [], [zero, noProof], [{p: {}, sts: [state(0)]}], {randomStates: 0, requests: 1})).toEqual([zero, noProof])
})
test('finite Houdini reaches a fixpoint as removed premises admit new predecessors', () => {
  const m: Machine = {name: 'cascade', params: [], inputs: [], state: {a: n(0), b: n(0)}, step: {state: {a: n(1), b: x('a')}}}
  const a = {name: 'a zero', holds: same(x('a'), n(0))}, b = {name: 'b zero', holds: same(x('b'), n(0))}
  const drops: [number, string][] = []
  const samples = [{p: {}, sts: [0, 1].map(a => ({scalars: {a, b: 0}, maps: {}}))}]
  expect(finiteHoudini(m, m, [], [a, b], samples, {randomStates: 0, requests: 1, onDrop: d => drops.push([d.round, d.law.name])})).toEqual([])
  expect(drops).toEqual([[0, 'a zero'], [1, 'b zero']])
  expect(finiteHoudini(m, m, [a], [a, b], samples, {randomStates: 0, requests: 1})).toEqual([a, b])
})

test('a completed model is a CTI only after a real step from the whole family', () => {
  const m = counter(), law = {name: 'zero', holds: same(x('value'), n(0))}, check = finiteModelChecker(m)
  expect(check([law], law, {value: 0}).genuine).toBe(true)
  expect(check([law], law, {value: 1}).genuine).toBe(false)
  expect(check([law, {name: 'inconsistent', holds: same(x('value'), n(1))}], law, {value: 0}).genuine).toBe(false)
  expect(check([law], law, {value: 0}, () => true).genuine).toBe(false)
  const unchanged = {...m, step: {}}
  expect(finiteModelChecker(unchanged)([law], law, {value: 0}).genuine).toBe(false)
})
test('finite model certification recomputes count cells and rejects bad requests', () => {
  const m: Machine = {name: 'count completion', params: [], inputs: ['op'], state: {}, maps: {A: 0}, assume: same(x('op'), n(1)), counts: {Total: {j: 'row', key: 'key', below: n(2), body: get('A', x('key'))}}, step: {maps: {A: {key: n(0), value: n(1)}}}}
  const law = {name: 'empty', holds: same(get('Total', n(0)), n(0))}, check = finiteModelChecker(m)
  expect(check([law], law, {op: 1, 'Total[]': 999}).genuine).toBe(true)
  expect(check([law], law, {op: 0}).genuine).toBe(false)
  expect(check([law], law, {op: 1, a: 0, b: 0, 'A[a:1]': 0, 'A[b:1]': 1}).genuine).toBe(false)
  expect(check([law], law, {op: -1}).genuine).toBe(false)
})
test('an unsupported predecessor law cannot certify a finite model', () => {
  const m = counter(), zero = {name: 'zero', holds: same(x('value'), n(0))}
  const unsupported: Law = {name: 'unbounded', forall: 'i', holds: same(times(2, x('i')), x('i'))}
  expect(finiteModelChecker(m)([zero, unsupported], zero, {value: 0}).genuine).toBe(false)
})

test('finite frontiers expose both one-sided cube boundaries and field limits', () => {
  const a = same(x('a'), n(1)), b = same(x('b'), n(1)), cube: Law = {name: 'cube', holds: not(all(a, b))}
  const frontiers = lawFrontiers(cube)
  expect(frontiers).toContainEqual([a, not(b)])
  expect(frontiers).toContainEqual([b, not(a)])
  expect(lawFrontiers({name: 'bound', holds: atMost(x('a'), n(2))})).toEqual([[same(x('a'), n(2))]])
})
test('finite boundary states update real count bodies without mutating samples', () => {
  const source: Machine = {name: 'row', params: ['n'], inputs: [], state: {ready: n(0)}, maps: {Rows: 0}, step: {}}
  const m: Machine = {...source, counts: {Count: {j: 'row', key: 'member', below: x('n'), body: ite(same(get('Rows', plus(times(8, x('row')), x('member'))), n(1)), n(1), n(0))}}}
  const old: State = {scalars: {ready: 0}, maps: {Rows: new Map()}}, condition = same(get('Count', n(1)), n(2))
  const st = boundaryState(source, m, [condition, same(x('ready'), n(1))], {n: 3}, old, {})!
  expect(st).toBeDefined()
  expect(finiteEvaluator(m)({name: 'boundary', holds: condition}, {n: 3}, st)).toBe(true)
  expect(st.scalars.ready).toBe(1)
  expect(old.maps.Rows!.size).toBe(0)
  expect(old.scalars.ready).toBe(0)
  expect(boundaryState(source, m, [same(get('Count', n(0)), n(4))], {n: 3}, old, {})).toBeUndefined()
})

test('a finite sampling allowance returns survivors but never extends the outer wall', () => {
  const m = counter(), law = {name: 'zero', holds: same(x('value'), n(0))}, results: {timedOut: boolean, dropped: number, ms: number}[] = []
  expect(finiteHoudini(m, m, [], [law], [{p: {}, sts: [state(0)]}], {wallMs: 0, onFinish: row => results.push(row)})).toEqual([law])
  expect(results).toEqual([{timedOut: true, dropped: 0, ms: expect.any(Number)}])
})

test('completed finite drops survive cancellation of the rest of the local pass', () => {
  const m = counter(), law = {name: 'zero', holds: same(x('value'), n(0))}
  expect(finiteHoudini(m, m, [], [law], [{p: {}, sts: [state(0)]}], {randomStates: 0, requests: 1, onDrop: () => { throw new WallExpired('after certified drop') }})).toEqual([])
})

test('finite filtering obeys the outer wall rather than extending it', () => {
  const m = counter()
  expect(() => withWall(-Infinity, () => finiteHoudini(m, m, [], [], [{p: {}, sts: [state(0)]}], {randomStates: 1}))).toThrow(WallExpired)
})
