import {expect,test} from 'bun:test'
import {type Machine,n,same} from '../machine.ts'
import {clock,counted,fullRate,withWall} from '../../kernel/prove.ts'
import {proveCountCases} from '../count-cases.ts'
import {proveFocusedCounts} from '../count-focus-proof.ts'
import {fieldBoundLemmas} from './field-bound-lemmas.ts'

test('an expired source budget returns before inspecting machine rows',()=>{
 const machine=new Proxy({} as Machine,{get(){throw new Error('expired source inspected machine')}}),trace:object[]=[]
 const result=fieldBoundLemmas(machine,[],{name:'expired source',hyps:[]},{reads:[],insts:[]},clock()-1,trace)
 expect(result).toBeUndefined()
 expect(trace).toEqual([{stage:'source-budget-exhausted'}])
})
test('an expired wall stops source construction even when counted work remains',()=>{
 const machine=new Proxy({} as Machine,{get(){throw new Error('wall-expired source inspected machine')}}),goal={name:'expired wall',hyps:[]},cert={reads:[],insts:[]},trace:object[]=[]
 withWall(0,()=>counted(fullRate,()=>{
  const until=clock()+1000
  expect(fieldBoundLemmas(machine,[],goal,cert,until,trace)).toBeUndefined()
  expect(proveCountCases(machine,[],{},cert,until,()=>{throw new Error('wall-expired case rebuilt a goal')})).toBeUndefined()
  expect(proveFocusedCounts(machine,[],{name:'unused',holds:same(n(0),n(0))},{},until,()=>{throw new Error('wall-expired focus proposed a certificate')})).toBeUndefined()
 },true))
 expect(trace).toEqual([{stage:'source-budget-exhausted'}])
})
