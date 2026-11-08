import {expect, test} from 'bun:test'
import {type Law, type Machine, all, any, atMost, get, less, n, not, plus, same, times, x} from '../core/machine.ts'
import {assumed, check} from './kernel.ts'
import {clock, grow, modelInstances} from './prove.ts'
import {modelValueTerms} from './model-values.ts'

test('function arguments keep symbolic keys rather than arithmetic neighbours', () => {
  const a=x('a'),b=x('b'),body=any(not(same(get('f',a),get('f',b))),same(a,b))
  // Frozen input: with a already assigned 5, b=a used to propose 5,6,4.
  expect(modelValueTerms(body,'b',new Set(['b']),e=>e.op==='var'&&e.name==='a'?5:undefined)).toEqual([])
  const packed=atMost(plus(x('index'),n(1)),get('Table',plus(x('index'),n(2))))
  expect(modelValueTerms(packed,'index',new Set(['index']),()=>10)).toEqual([])
})

test('arithmetic-only boundaries remain available and ordered', () => {
  const body=atMost(times(2,x('half')),get('Total',n(0)))
  expect(modelValueTerms(body,'half',new Set(['half']),e=>e.op==='get'?14:undefined)).toEqual([n(7),n(8),n(6)])
})

test('an arithmetic witness stays constant when its value equals a row key', () => {
  const machine: Machine = {name:'aliased half',params:[],inputs:[],state:{},maps:{A:0,Good:0},step:{}}
  const a=get('A',x('row')), twice=times(2,x('half'))
  const law:Law={name:'half',forall:'row',keys:['half'],holds:any(not(all(atMost(twice,a),less(a,plus(twice,n(2))))),same(get('Good',x('row')),n(1)))}
  const goal={name:'half aliases row',hyps:[same(get('A',x('root')),n(14)),same(get('Good',x('root')),n(0))]}
  const found=modelInstances(machine,[law],{},goal,{root:7,'A[root:1]':14,'Good[root:1]':0})
  expect(found?.[law.name]).toEqual([x('root'),n(7)])
})

// Non-key naturals are not drawn from the map-key domain. A model with one row
// can still need half-cardinality witnesses 7 and 5 to instantiate a law.
test('model instances obtain arithmetic-only witnesses from comparison boundaries', () => {
  const machine: Machine = {name: 'halves', params: [], inputs: [], state: {}, maps: {A: 0, B: 0, Good: 0}, step: {}}
  const a = get('A', x('row')), b = get('B', x('row'))
  const twice = (s: string) => times(2, x(s))
  const law: Law = {name: 'matching halves certify the row', forall: 'row', keys: ['halfA', 'halfB'], holds: any(not(all(
    atMost(twice('halfA'), a), less(a, plus(twice('halfA'), n(2))),
    atMost(twice('halfB'), b), less(b, plus(twice('halfB'), n(2))))), same(get('Good', x('row')), n(1)))}
  const goal = {name: 'a bad row at its halves', hyps: [same(get('A', n(0)), n(14)), same(get('B', n(0)), n(10)), same(get('Good', n(0)), n(0))]}
  const witness = {'A[]': 14, 'B[]': 10, 'Good[]': 0}
  const instances = modelInstances(machine, [law], {}, goal, witness)
  expect(instances?.[law.name]).toContainEqual(n(7))
  expect(instances?.[law.name]).toContainEqual(n(5))
  if (!instances) return
  const refined = {name: goal.name, hyps: [...goal.hyps, ...assumed([law], instances)]}
  const proof = grow(refined, new Map(), {nodes: 0, until: clock() + 1500})
  expect('tree' in proof).toBe(true)
  if ('tree' in proof) expect(check(refined, proof.tree)).toBe(true)
})
