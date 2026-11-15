import {describe, expect, test} from 'bun:test'
import type {Law, Machine, E, C} from '../../core/machine.ts'
import {proveCandidateSeeds} from '../../core/candidate-seeds.ts'
import {restateSeeds} from './candidate-seed-restatement.ts'
const v=(name:string):E=>({op:'var',name}), n=(value:number):E=>({op:'const',value})
const target:Machine={name:'tuple',params:['nodes','keys'],inputs:[],state:{},maps:{Owner:0},relations:{Owner:['Key','Node']},step:{}}
const bindings={maps:{Owner:{target:'Owner',sorts:['Key','Node'],radix:64}},domains:{Key:'keys',Node:'nodes'}}
const packed:E={op:'add',a:{op:'mul',k:64,a:v('k')},b:v('i')}
const source:Law={name:'example',forall:'k',keys:['i'],holds:{op:'or',xs:[{op:'not',x:{op:'<',a:v('k'),b:n(64)}},{op:'not',x:{op:'<',a:v('i'),b:n(64)}},{op:'=',a:{op:'get',map:'Owner',key:packed},b:n(0)}]}}
describe('candidate restatement',()=>{
 test('maps packed positions and only explicit guards to symbolic bounds',()=>{
  const [a]=restateSeeds([source],target,bindings);expect(a?.status).toBe('candidate')
  if(a?.status!=='candidate')return
  expect(a.bindings).toEqual({k:'Key',i:'Node'})
  expect(a.law.holds).toEqual({op:'or',xs:[{op:'not',x:{op:'<',a:v('k'),b:v('keys')}},{op:'not',x:{op:'<',a:v('i'),b:v('nodes')}},{op:'=',a:{op:'get',map:'Owner',key:{op:'tup',a:v('k'),b:v('i')}},b:n(0)}]})
 })
 test('drops an unclassified binder and ambiguous radix literal',()=>{
  const unclassified={...source,keys:['i','j']}
  const ambiguous={...source,holds:{op:'=',a:{op:'get',map:'Owner',key:packed},b:n(64)} as C}
  const a=restateSeeds([unclassified,ambiguous],target,bindings)
  expect(a.map(x=>x.status)).toEqual(['dropped','dropped'])
 })
 test('drops incompatible target layout',()=>{
  expect(restateSeeds([source],{...target,relations:{Owner:['Node','Key']}},bindings)[0]?.status).toBe('dropped')
 })
})
describe('candidate closure',()=>{
 const m:Machine={name:'constant',params:[],inputs:[],state:{x:n(0)},step:{state:{x:n(0)}}}
 const good:Law={name:'zero',holds:{op:'=',a:v('x'),b:n(0)}}
 const bad:Law={name:'false at start',holds:{op:'=',a:v('x'),b:n(1)}}
 test('false seed is discarded before whole-family kernel check',()=>{
  const result=proveCandidateSeeds(m,[good],[bad])
  expect(result.status).toBe('checked')
  if(result.status==='checked'){expect(result.kept).toEqual([]);expect(result.dropped.map(d=>d.name)).toEqual(['false at start']);expect(result.closure.checked).toBe(true)}
 })
 test('duplicate names and existential metadata are refused',()=>{
  expect(()=>proveCandidateSeeds(m,[good],[good])).toThrow()
  expect(proveCandidateSeeds(m,[good],[{...bad,some:['z']}]).status).toBe('inconclusive')
 })
})
