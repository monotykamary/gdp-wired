import {expect,test} from 'bun:test'
import {type Machine,any,atMost,ite,less,n,same,x} from './machine.ts'
import {type Goal,checkMC} from '../kernel/kernel.ts'
import {atPoint,clock} from '../kernel/prove.ts'
import {proveCountCases} from './count-cases.ts'

const action=x('action'),value=x('value'),cases=[0,1,2].map(k=>same(action,n(k)))
const m:Machine={name:'renamed finite choices',params:[],inputs:['action'],state:{},maps:{},assume:any(...cases),step:{}}
const goal=(bound:number):Goal=>({name:'finite choices @step',hyps:[m.assume!,atMost(action,n(2)),same(value,ite(cases[0]!,n(3),ite(cases[1]!,n(4),n(5)))),less(value,n(bound))]})

test('finite count recovery returns an original-kernel-checked tree and restores search scope',()=>{
  const before=atPoint.on,packet={goal:goal(3),decls:[]},cert={reads:[],insts:[]}
  const result=proveCountCases(m,[],{},cert,clock()+2000,()=>packet)
  expect(result).toBeDefined()
  if(result)expect(checkMC(packet.goal.hyps,[],result.cert)).toBe(true)
  expect(atPoint.on).toBe(before)
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
