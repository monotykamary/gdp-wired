import {describe, expect, test} from 'bun:test'
import type {C, E, Law, Machine} from '../../core/machine.ts'
import {restateSeeds} from './candidate-seed-restatement.ts'

const v=(name:string):E=>({op:'var',name})
const tup=(a:E,b:E):E=>({op:'tup',a,b})
const read=(map:string,key:E):E=>({op:'get',map,key})
const eq=(a:E,b:E):C=>({op:'=',a,b})
const machine:Machine={name:'native tuple seeds',params:['as','bs','cs'],inputs:[],state:{},maps:{Pair:0,Triple:0},relations:{Pair:['A','B'],Triple:['A','B','C']},step:{}}
const config={maps:{Pair:{target:'Pair',sorts:['A','B'],radix:64},Triple:{target:'Triple',sorts:['A','B','C'],radix:64}},domains:{A:'as',B:'bs',C:'cs'}}
const law=(key:E,map='Pair'):Law=>({name:'native',forall:'x',keys:['y',...(map==='Triple'?['z']:[])],holds:eq(read(map,key),{op:'const',value:0})})

describe('native source tuple restatement',()=>{
 test('binary and right-associated ternary retain coordinate order and add no bounds',()=>{
  for(const [l,expected] of [[law(tup(v('x'),v('y'))),{x:'A',y:'B'}],[law(tup(v('x'),tup(v('y'),v('z'))),'Triple'),{x:'A',y:'B',z:'C'}]] as const){
   const a=restateSeeds([l],machine,config)[0]
   expect(a?.status).toBe('candidate'); if(a?.status!=='candidate')throw Error('unexpected refusal')
   expect(a.bindings).toEqual(expected); expect(a.law.holds).toEqual(l.holds)
   expect(a.unboundedBinders).toEqual(Object.keys(expected))
  }
 })
 test('arity, association, nonvariable coordinates, and target layout mismatch are refused',()=>{
  const cases=[law(tup(v('x'),tup(v('y'),v('z')))),law(tup(v('x'),v('y')),'Triple'),law(tup(tup(v('x'),v('y')),v('z')),'Triple'),law(tup(v('x'),{op:'const',value:0}))]
  expect(restateSeeds(cases,machine,config).every(a=>a.status==='dropped')).toBe(true)
  expect(restateSeeds([law(tup(v('x'),v('y')))],{...machine,relations:{...machine.relations,Pair:['B','A']}},config)[0]?.status).toBe('dropped')
 })
 test('permuted variables preserve positions and conflicting use fails closed',()=>{
  const swapped=law(tup(v('y'),v('x')))
  const a=restateSeeds([swapped],machine,config)[0]
  expect(a?.status).toBe('candidate');if(a?.status!=='candidate')throw Error('unexpected refusal')
  expect(a.bindings).toEqual({y:'A',x:'B'});expect(a.law.holds).toEqual(swapped.holds)
  const conflicting:Law={...swapped,holds:{op:'and',xs:[swapped.holds,eq(read('Pair',tup(v('x'),v('y'))),{op:'const',value:0})]}}
  expect(restateSeeds([conflicting],machine,config)[0]?.status).toBe('dropped')
 })
})
