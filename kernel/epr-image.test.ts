import {expect, test} from 'bun:test'
import {type E, type C, n, x} from '../core/machine.ts'
import {decide} from './epr.ts'
import {type Goal, check} from './kernel.ts'
import {grow, eprScope, withWall} from './prove.ts'
const eq = (a: E,b: E): C => ({op:'=',a,b})
const get = (map: string,key: E): E => ({op:'get',map,key})
const pair = (a: E,b: E): E => ({op:'tup',a,b})
const cell = (a: E) => get('R',pair(a,a))
const fp=get('F',x('p')), fq=get('F',x('q'))
const updated: E={op:'if',c:eq(x('p'),x('q')),then:{op:'if',c:eq(x('mode'),n(0)),then:x('a'),else:fp},else:fq}
const patterns={R:[0,0],F:[0]}
test('correlated updates in tuple keys retain the eight-leaf normalization bound',()=>{
  const g: Goal={name:'correlated tuple update',hyps:[eq(cell(x('a')),n(0)),eq(cell(fp),n(0)),eq(cell(fq),n(0)),eq(cell(updated),n(1))]}
  const d=decide(g,patterns,{exact:true}); expect('sat'in d && !d.sat).toBe(true)
  const old=eprScope.patterns; eprScope.patterns=patterns
  try {const out=withWall(performance.now()+5000,()=>grow(g));expect('tree'in out).toBe(true);if('tree'in out)expect(check(g,out.tree)).toBe(true)}finally{eprScope.patterns=old}
  const sat=decide({name:'reachable updated tuple',hyps:[eq(x('p'),x('q')),eq(x('mode'),n(0)),eq(cell(x('a')),n(1)),eq(cell(updated),n(1))]},patterns,{exact:true})
  expect('sat'in sat && sat.sat).toBe(true)
},15000)
test('tuple-shape caches are scoped to function-map classification',()=>{
  const g: Goal={name:'function shape scope',hyps:[eq(cell(fp),n(0)),eq(cell(fp),n(1))]}
  expect('unknown'in decide(g,{R:[0,0],F:[1]},{exact:true})).toBe(true)
  const d=decide(g,patterns,{exact:true});expect('sat'in d && !d.sat).toBe(true)
  expect('unknown'in decide(g,{R:[0,0],F:[1]},{exact:true})).toBe(true)
})
test('opaque arithmetic may be irrelevant to a refutation but never validates an exact model',()=>{
  const opaque=eq({op:'prod',a:x('u'),b:x('v')},n(2)), r=get('B',x('k'))
  const d=decide({name:'irrelevant opaque',hyps:[opaque,eq(r,n(0)),eq(r,n(1))]},{B:[1]},{exact:true})
  expect('sat'in d && !d.sat).toBe(true)
  expect('unknown'in decide({name:'unsupported exact model',hyps:[opaque,eq(r,n(1))]},{B:[1]},{exact:true})).toBe(true)
})
