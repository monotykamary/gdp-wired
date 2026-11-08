import {expect,test} from 'bun:test'
import {type Machine,any,atMost,get,ite,less,n,not,same,x} from './machine.ts'
import {type CountCert,type CountDecl,type Goal,type Instances,checkMC,substC} from '../kernel/kernel.ts'
import {atPoint,clock} from '../kernel/prove.ts'
import {proveCountCases,selectCountBounds,withoutCountWitnesses} from './count-cases.ts'

const action=x('action'),value=x('value'),cases=[0,1,2].map(k=>same(action,n(k)))
const m:Machine={name:'renamed finite choices',params:[],inputs:['action'],state:{},maps:{},assume:any(...cases),step:{}}
const goal=(bound:number):Goal=>({name:'finite choices @step',hyps:[m.assume!,atMost(action,n(2)),same(value,ite(cases[0]!,n(3),ite(cases[1]!,n(4),n(5)))),less(value,n(bound))]})

test('finite count recovery returns an original-kernel-checked tree and restores search scope',()=>{
  const before=atPoint.on,packet={goal:goal(3),decls:[]},cert={reads:[],insts:[]},events:Record<string,unknown>[]=[]
  const result=proveCountCases(m,[],{},cert,clock()+2000,()=>packet,{trace:e=>events.push(e)})
  expect(result).toBeDefined()
  expect(events.some(e=>e.stage==='case-fallback'&&e.proposed)).toBe(true)
  if(result)expect(checkMC(packet.goal.hyps,[],result.cert)).toBe(true)
  expect(atPoint.on).toBe(before)
})

test('finite cases use checked activation and witness derivations without an opt-in',()=>{
 const machine:Machine={...m,counts:{Rows:{j:'row',key:'member',below:n(2),body:n(0)}},step:{flags:{active:same(action,n(0))}}}
 const decls:CountDecl[]=[{map:'Rows',...machine.counts!.Rows!}],cert:Pick<CountCert,'reads'|'insts'>={reads:[['r','Rows',n(0)]],insts:[{wit:'memberWitness',below:n(2),terms:[[1,'r']],unit:0}]}
 const packet={goal:{name:'zero row @step',hyps:[m.assume!,less(n(0),get('Rows',n(0)))]},decls},events:Record<string,unknown>[]=[]
 const result=proveCountCases(machine,[],{},cert,clock()+2000,()=>packet,{trace:e=>events.push(e)})
 expect(result).toBeDefined()
 expect(events.some(e=>e.stage==='case-derivations'&&e.proposed)).toBe(true)
 if(result)expect(checkMC(packet.goal.hyps,decls,result.cert)).toBe(true)
})

test('ranked bounds use the arithmetic core rather than every preceding proposal',()=>{
 const base={name:'numeric selection',hyps:[less(n(0),x('needed'))]},candidates=[{index:7,bound:atMost(x('unused'),n(4))},{index:2,bound:atMost(x('needed'),n(0))},{index:9,bound:atMost(x('later'),n(0))}]
 const picked=selectCountBounds(base,candidates,clock()+1000)
 expect(picked?.indices).toEqual([2]);expect(picked?.fallback).toBe(false)
 expect(selectCountBounds(base,candidates,clock()-1)).toBeUndefined()
})

test('default case recovery excludes a false bound and retains the successful slim certificate',()=>{
 const decls:CountDecl[]=[{map:'Rows',j:'j',key:'k',below:n(2),body:n(1)}]
 const cert:Pick<CountCert,'reads'|'insts'>={reads:[['r','Rows',n(0)]],insts:[{wit:'bad',below:n(2),terms:[[1,'r']],unit:0},{wit:'good',below:n(2),terms:[[1,'r']],unit:-1}]}
 const packet={goal:{name:'bounded count @step',hyps:[m.assume!,less(n(2),get('Rows',n(0)))]},decls},events:Record<string,unknown>[]=[]
 const result=proveCountCases(m,[],{},cert,clock()+3000,()=>packet,{trace:e=>events.push(e)})
 expect(result).toBeDefined()
 expect(events.some(e=>e.stage==='count-core-excluded'&&e.index===0)).toBe(true)
 if(result){expect(result.cert.insts.map(i=>i.wit)).toEqual(['good']);expect(checkMC(packet.goal.hyps,decls,result.cert)).toBe(true)}
 expect(cert.insts).toHaveLength(2)
})

test('selected cases retain newly seeded universal-flag witnesses in the final source',()=>{
 const q=same(get('Q',x('k')),n(1)),a=same(get('A',x('k')),n(1)),predicate=any(not(q),a)
 const machine:Machine={...m,inputMaps:['Q'],maps:{Q:0,A:0},step:{flags:{eligible:{op:'all',key:'k',c:predicate}}}}
 const decls:CountDecl[]=[{map:'Requested',j:'unused',key:'k',below:n(4),body:ite(q,n(1),n(0))},{map:'Allowed',j:'unused',key:'k',below:n(4),body:ite(a,n(1),n(0))}]
 const cert:Pick<CountCert,'reads'|'insts'>={reads:[['rq','Requested',n(0)],['ra','Allowed',n(0)]],insts:[{wit:'unused',below:n(4),terms:[[1,'ra'],[-1,'rq']],unit:0},{wit:'needed',below:n(4),terms:[[1,'rq'],[-1,'ra']],unit:0}]}
 const build=(at:Instances)=>({decls,goal:{name:'flag-backed subset @step',hyps:[m.assume!,less(get('Allowed',n(0)),get('Requested',n(0))),...(at['?eligible']??[]).map(key=>substC(predicate,{vars:{k:key},maps:{},flags:{}}))]}})
 const result=proveCountCases(machine,[],{},cert,clock()+3000,build)
 expect(result).toBeDefined()
 if(result){
  expect(result.cert.insts.map(i=>i.wit)).toEqual(['needed'])
  expect(result.instances['?eligible']).toContainEqual(x('needed'))
  expect(checkMC(build(result.instances).goal.hyps,decls,result.cert)).toBe(true)
 }
})

test('an arithmetic core of an unprovable bound cannot certify a false law',()=>{
 const decls:CountDecl[]=[{map:'Rows',j:'j',key:'k',below:n(2),body:n(1)}],cert:Pick<CountCert,'reads'|'insts'>={reads:[['r','Rows',n(0)]],insts:[{wit:'falseBound',below:n(2),terms:[[1,'r']],unit:0}]}
 const packet={goal:{name:'false zero-count claim @step',hyps:[m.assume!,less(n(0),get('Rows',n(0)))]},decls},events:Record<string,unknown>[]=[]
 expect(proveCountCases(m,[],{},cert,clock()+1500,()=>packet,{trace:e=>events.push(e)})).toBeUndefined()
 expect(events.some(e=>e.stage==='count-core-excluded')).toBe(true)
})

test('slimming witness instances removes complete tuples without mutating the caller',()=>{
 const law={name:'rows',forall:'a',keys:['b'],holds:atMost(x('a'),x('b'))},at={rows:[x('keep'),x('b'),x('drop'),x('b')]}
 expect(withoutCountWitnesses(m,[law],at,new Set(['drop'])).rows).toEqual([x('keep'),x('b')])
 expect(at.rows).toHaveLength(4)
})

test('compact recovery keeps its saturated branches and local model scope checked',()=>{
  const options={localModels:true,saturate:true,queryMs:300,coreLimit:16,units:false,corePointOnly:true},before=atPoint.on
  const packet={goal:goal(3),decls:[]},result=proveCountCases(m,[],{}, {reads:[],insts:[]},clock()+2000,()=>packet,options)
  expect(result).toBeDefined()
  if(result)expect(checkMC(packet.goal.hyps,[],result.cert)).toBe(true)
  expect(proveCountCases(m,[],{}, {reads:[],insts:[]},clock()+1000,()=>({goal:goal(6),decls:[]}),options)).toBeUndefined()
  expect(atPoint.on).toBe(before)
})

test('finite count recovery does not turn a satisfiable goal into a proof',()=>{
  const before=atPoint.on
  expect(proveCountCases(m,[],{}, {reads:[],insts:[]},clock()+1000,()=>({goal:goal(6),decls:[]}))).toBeUndefined()
  expect(atPoint.on).toBe(before)
})
