import {test,expect} from 'bun:test'
import {get,n,x,less} from '../machine.ts'
import {linear,type Path} from '../../kernel/kernel.ts'
import {fieldAttemptObserver,fieldDemandAt,observeFieldLeaf,recordFieldAttempt,beginFieldAttempt,endFieldAttempt,type FieldAttempt} from './field-demand.ts'
import {leafAllowance} from './leaf-allowance.ts'
test('active leaf draws conserve the original allowance and never extend it',()=>{for(const remaining of [0,1,500,2700,5000]){const start=12,until=start+remaining,end=Math.min(until,start+leafAllowance(remaining,1));expect(end).toBeLessThanOrEqual(until);expect(end-start).toBeCloseTo(remaining/3,8)}})
test('field demand distinguishes core, model, absence and missing observation',()=>{
 const path:Path=new Map(),events:FieldAttempt[]=[],cell=get('A',x('i')),other=get('B',x('i')),col=Object.keys(linear(cell,path)!)[0]!
 fieldAttemptObserver.on=e=>events.push(e)
 try{observeFieldLeaf({name:'leaf',hyps:[less(cell,n(3))]},path,{core:[0],witness:{[col]:1}})
 const demand=fieldDemandAt(path);expect(demand?.coreColumns).toContain(col)
 for(const a of [cell,other])recordFieldAttempt({op:'<=',a,b:n(3)},path,demand,11,false,'test')
 recordFieldAttempt({op:'<=',a:other,b:n(3)},path,undefined,7,false,'test')
 expect(events.map(e=>e.requested)).toEqual([true,false,undefined]);expect(events.map(e=>e.units)).toEqual([11,11,7])
 }finally{fieldAttemptObserver.on=undefined}
})
test('a parent observation cannot claim demand absence at a stronger child scope',()=>{
 const events:FieldAttempt[]=[],path:Path=new Map();fieldAttemptObserver.on=e=>events.push(e)
 try{observeFieldLeaf({name:'parent',hyps:[]},path,{witness:{}});const demand=fieldDemandAt(path),child=new Map(path).set('branch',{lin:{branch:1},holds:true});recordFieldAttempt(less(x('cell'),n(2)),child,demand,1,false,'test');expect(events[0]!.requested).toBeUndefined()}finally{fieldAttemptObserver.on=undefined}
})
test('nested attempt costs are exclusive and both are recorded on unwind',()=>{
 const events:FieldAttempt[]=[],path:Path=new Map(),candidate=less(x('a'),n(2));fieldAttemptObserver.on=e=>events.push(e)
 try{const parent=beginFieldAttempt(candidate,path,undefined,'parent'),child=beginFieldAttempt(candidate,path,undefined,'child');endFieldAttempt(child,false);endFieldAttempt(parent,false)
 expect(events).toHaveLength(2);expect(events[0]!.parent).toBe(events[1]!.id);expect(events[0]!.units+events[1]!.units).toBeCloseTo(events[1]!.inclusiveUnits!,8)
 }finally{fieldAttemptObserver.on=undefined}
})
test('disabled observer does not inspect a goal or alter the candidate',()=>{
 fieldAttemptObserver.on=undefined
 observeFieldLeaf(new Proxy({} as any,{get(){throw Error('inspected')}}),new Map(),{})
 expect(fieldDemandAt(new Map())).toBeUndefined()
})
