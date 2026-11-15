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
 test('restates sized unary native maps without relation metadata',()=>{
  for(const map of ['HasLock','Semaphore']) {
   const unary:Machine={name:'unary',params:['nodes'],inputs:[],state:{},maps:{[map]:0},step:{}}
   const cfg={maps:{[map]:{target:map,sorts:['Node'],radix:64}},domains:{Node:'nodes'}}
   const law:Law={name:'unary guarded',forall:'i',holds:{op:'or',xs:[{op:'not',x:{op:'<',a:v('i'),b:n(64)}},{op:'<=',a:{op:'get',map,key:v('i')},b:n(1)}]}}
   const [a]=restateSeeds([law],unary,cfg)
   expect(a?.status).toBe('candidate')
   if(a?.status!=='candidate')throw Error('unary restatement failed')
   expect(a.bindings).toEqual({i:'Node'})
   expect(a.law.holds).toEqual({op:'or',xs:[{op:'not',x:{op:'<',a:v('i'),b:v('nodes')}},{op:'<=',a:{op:'get',map,key:v('i')},b:n(1)}]})
   expect(restateSeeds([law],{...unary,relations:{[map]:['Other']}},cfg)[0]?.status).toBe('dropped')
   expect(restateSeeds([law],{...unary,params:[]},cfg)[0]?.status).toBe('dropped')
   expect(restateSeeds([law],{...unary,maps:{}},cfg)[0]?.status).toBe('dropped')
  }
 })
 test('restates declared count-map reads with explicit logical arguments',()=>{
  const counted:Machine={name:'counts',params:['values','nodes'],inputs:[],state:{},step:{},counts:{Votes:{j:'j',key:'k',below:v('nodes'),body:n(0)}}}
  const cfg={maps:{OldVotes:{target:'Votes',sorts:['Value'],radix:64}},domains:{Value:'values'}}
  const law:Law={name:'count bound',forall:'i',holds:{op:'or',xs:[{op:'not',x:{op:'<',a:v('i'),b:n(64)}},{op:'<=',a:{op:'get',map:'OldVotes',key:v('i')},b:n(1)}]}}
  const [a]=restateSeeds([law],counted,cfg)
  expect(a?.status).toBe('candidate')
  if(a?.status!=='candidate')throw Error('count restatement failed')
  expect(a.law.holds).toEqual({op:'or',xs:[{op:'not',x:{op:'<',a:v('i'),b:v('values')}},{op:'<=',a:{op:'get',map:'Votes',key:v('i')},b:n(1)}]})
  expect(restateSeeds([law],{...counted,counts:{}},cfg)[0]?.status).toBe('dropped')
  expect(restateSeeds([law],{...counted,maps:{Votes:0}},cfg)[0]?.status).toBe('dropped')
 })
 test('explicit tuple coordinates work for numeric native maps of any value kind',()=>{
  const numeric:Machine={name:'numeric tuple',params:['nodes','keys'],inputs:[],state:{},maps:{Table:0},step:{}}
  const cfg={maps:{Table:{target:'Table',sorts:['Node','Key'],radix:64}},domains:{Node:'nodes',Key:'keys'}}
  const law:Law={name:'numeric cell',forall:'k',keys:['i'],holds:{op:'or',xs:[{op:'not',x:{op:'<',a:v('k'),b:n(64)}},{op:'not',x:{op:'<',a:v('i'),b:n(64)}},{op:'<=',a:{op:'get',map:'Table',key:packed},b:n(7)}]}}
  const [a]=restateSeeds([law],numeric,cfg)
  expect(a?.status).toBe('candidate')
  if(a?.status!=='candidate')throw Error('numeric tuple restatement failed')
  expect(a.bindings).toEqual({k:'Node',i:'Key'})
  expect(a.law.holds).toEqual({op:'or',xs:[{op:'not',x:{op:'<',a:v('k'),b:v('nodes')}},{op:'not',x:{op:'<',a:v('i'),b:v('keys')}},{op:'<=',a:{op:'get',map:'Table',key:{op:'tup',a:v('k'),b:v('i')}},b:n(7)}]})
  expect(restateSeeds([law],numeric,{...cfg,maps:{}})[0]?.status).toBe('dropped')
  expect(restateSeeds([law],{...numeric,relations:{Table:['Key','Node']}},cfg)[0]?.status).toBe('dropped')
 })
 test('constant count keys require a genuinely index-independent declaration',()=>{
  const count={j:'j',key:'k',below:v('nodes'),body:n(1)}
  const m:Machine={name:'constant count',params:['nodes'],inputs:[],state:{},step:{},counts:{Members:count}}
  const cfg={maps:{Old:{target:'Members',sorts:['Node'],radix:64}},domains:{Node:'nodes'}}
  const law:Law={name:'count total',holds:{op:'<=',a:{op:'get',map:'Old',key:n(0)},b:v('nodes')}}
  const [a]=restateSeeds([law],m,cfg)
  expect(a?.status).toBe('candidate')
  if(a?.status!=='candidate')throw Error('constant count not mapped')
  expect(a.law.holds).toEqual({op:'<=',a:{op:'get',map:'Members',key:n(0)},b:v('nodes')})
  expect(restateSeeds([law],{...m,counts:{Members:{...count,body:v('j')}}},cfg)[0]?.status).toBe('dropped')
 })
 test('unconditional binders stay unbounded instead of acquiring a domain assumption',()=>{
  const law:Law={name:'unconditional',forall:'k',keys:['i'],holds:{op:'=',a:{op:'get',map:'Owner',key:packed},b:n(0)}}
  const [a]=restateSeeds([law],target,bindings)
  expect(a?.status).toBe('candidate')
  if(a?.status!=='candidate')throw Error('unconditional candidate failed')
  expect(a.unboundedBinders).toEqual(['k','i'])
  expect(a.law.holds).toEqual({op:'=',a:{op:'get',map:'Owner',key:{op:'tup',a:v('k'),b:v('i')}},b:n(0)})
 })
 test('drops an unclassified binder and ambiguous radix literal',()=>{
  const unclassified={...source,keys:['i','j'],holds:{op:'and',xs:[source.holds,{op:'<',a:v('j'),b:n(5)}]} as C}
  const ambiguous={...source,holds:{op:'=',a:{op:'get',map:'Owner',key:packed},b:n(64)} as C}
  const a=restateSeeds([unclassified,ambiguous],target,bindings)
  expect(a.map(x=>x.status)).toEqual(['dropped','dropped'])
 })
 test('expands whole-cell universals and removes only genuinely unused binders',()=>{
  const raw:Law={name:'empty before start',forall:'cell',holds:{op:'=',a:{op:'get',map:'Owner',key:v('cell')},b:n(0)}}
  const [a]=restateSeeds([raw],target,bindings)
  expect(a?.status).toBe('candidate')
  if(a?.status!=='candidate')throw Error('raw cell expansion failed')
  expect(a.cellBinders?.cell).toHaveLength(2)
  expect(JSON.stringify(a.law.holds)).toContain('"op":"tup"')
  const [b]=restateSeeds([{...source,keys:['i','unused']}],target,bindings)
  expect(b?.status).toBe('candidate')
  if(b?.status!=='candidate')throw Error('vacuous binder not eliminated')
  expect(b.vacuousBinders).toEqual(['unused']);expect(b.law.keys).toEqual(['i'])
 })
 test('explicit value-sort bindings restate numeric values without inferring a key sort',()=>{
  const m:Machine={name:'values',params:['nodes','values'],inputs:[],state:{},maps:{Vote:0},step:{}}
  const cfg={maps:{Vote:{target:'Vote',sorts:['Node'],radix:64}},domains:{Node:'nodes',Value:'values'}}
  const law:Law={name:'numeric value',forall:'n',keys:['v'],holds:{op:'or',xs:[{op:'not',x:{op:'<',a:v('n'),b:n(64)}},{op:'not',x:{op:'<',a:v('v'),b:n(64)}},{op:'=',a:{op:'get',map:'Vote',key:v('n')},b:{op:'add',a:v('v'),b:n(1)}}]}}
  expect(restateSeeds([law],m,cfg)[0]?.status).toBe('dropped')
  const [a]=restateSeeds([law],m,{...cfg,variables:{v:{sort:'Value',radix:64}}})
  expect(a?.status).toBe('candidate');if(a?.status!=='candidate')throw Error('value binding refused')
  expect(a.bindings).toEqual({v:'Value',n:'Node'})
  expect(JSON.stringify(a.law.holds)).toContain('"name":"values"')
  expect(restateSeeds([law],m,{...cfg,variables:{v:'Value',n:'Value'}})[0]?.status).toBe('dropped')
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
