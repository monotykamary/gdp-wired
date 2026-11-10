import {expect, test} from 'bun:test'
import {type Machine, type Request, type State, interpret, n, x, get, plus} from './machine.ts'
import {allowed} from './watch.ts'
import {sampleStep} from './sample-step.ts'
const m: Machine = {name: 'sample machine', params: ['size'], inputs: ['at', 'value'], inputMaps: ['carried'], state: {s: n(0)}, maps: {A: 0, B: 1},
  assume: {op: 'and', xs: [{op: 'flag', name: 'first'}, {op: 'flag', name: 'second'}]},
  step: {flags: {first: {op: '<', a: x('at'), b: x('size')}, second: {op: 'and', xs: [{op: 'flag', name: 'first'}, {op: '<=', a: x('value'), b: n(2)}]}},
    state: {s: plus(x('s'), n(1))}, maps: {A: {key: x('at'), value: get('B', x('at'))}, B: {key: x('at'), value: get('carried', x('at'))}}}}
const stateText = (s: State | undefined) => s && JSON.stringify([s.scalars, Object.entries(s.maps).map(([k,v])=>[k,[...v]]),s.defaults??{}])
test('hot sampler preserves accepted/refused requests, old-state reads and persistence', () => {
  const run = interpret(m), sampled = sampleStep(m, run), params = {size: 3}
  let state = run.init(params), accepted = 0, refused = 0
  for (let i = 0; i < 2400; i++) {
    const input: Request = {at: i % 5, value: i % 4, carried: new Map([[i % 5, i % 3]])}
    const before = stateText(state), expected = allowed(m, run, params, state, input) ? run.step(params, state, input) : undefined
    const next = sampled(params, state, input)
    expect(stateText(next)).toBe(stateText(expected)); expect(stateText(state)).toBe(before)
    if (next) { state = next; accepted++ } else refused++
  }
  expect(accepted).toBeGreaterThan(100); expect(refused).toBeGreaterThan(100)
})
test('no assumption keeps flags lazy, and evaluation errors still end a trial', () => {
  const machine: Machine = {...m, assume: undefined}, run = interpret(machine), sampled = sampleStep(machine, run)
  for (let i = 0; i < 1002; i++) expect(stateText(sampled({size: 3}, run.init({size: 3}), {at: 0, value: 1, carried: new Map()}))).toBe(stateText(run.step({size: 3}, run.init({size: 3}), {at: 0, value: 1, carried: new Map()})))
  expect(()=>sampled({size: 3}, run.init({size: 3}), {at: 0, carried: new Map()})).toThrow()
})
test('count-backed assumptions keep carried views and dependent flags', () => {
  const machine: Machine = {...m, counts: {count: {key: 'j', j: 'row', below: x('size'), body: get('carried', x('j'))}}, assume: {op: '<=', a: get('count', n(0)), b: n(1)}}
  const run = interpret(machine), sampled = sampleStep(machine, run), params = {size: 3}, state = run.init(params)
  for (let i=0;i<1100;i++) {
    const input: Request = {at: 0, value: 1, carried: new Map(Array.from({length: i%3},(_,j)=>[j,1]))}
    expect(stateText(sampled(params,state,input))).toBe(stateText(allowed(machine,run,params,state,input)?run.step(params,state,input):undefined))
  }
})
