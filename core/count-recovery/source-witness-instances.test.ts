import {expect,test} from 'bun:test'
import {any,get,n,not,plus,same,times,x,type Law,type Machine} from '../machine.ts'
import {assumed,check,type Goal,type Instances} from '../../kernel/kernel.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {sourceWitnessInstances} from './source-witness-instances.ts'

function fixture(){
 const cell=(row:ReturnType<typeof x>,member:ReturnType<typeof x>)=>get('Cells',plus(times(64,row),member)),a=x('a'),b=x('b'),member=x('sample')
 const law:Law={name:'matching rows agree',forall:'row',keys:['other','member'],holds:any(not(same(get('Tag',x('row')),get('Tag',x('other')))),same(cell(x('row'),x('member')),cell(x('other'),x('member'))))}
 const machine:Machine={name:'renamed field witness',params:[],inputs:[],state:{},maps:{Cells:0,Tag:0},counts:{Total:{j:'row',key:'member',below:n(4),body:n(1)}},step:{}}
 const goal:Goal={name:'source',hyps:[same(a,n(0)),same(b,n(1)),same(member,n(2)),same(get('Tag',a),n(0)),same(get('Tag',b),n(0)),same(cell(a,member),n(0)),same(cell(b,member),n(1))]}
 const result=modelSequence()(goal,clock()+1000)
 if('tree'in result||result.stuck!=='sat'||!result.witness)throw new Error('fixture must have a source model')
 return {machine,law,goal,model:result.witness}
}

test('local countermodels request ordinary multi-key field instances at a count witness',()=>{
 const {machine,law,goal,model}=fixture(),before:Instances={untouched:[x('prior')]},saved=JSON.stringify(before)
 const next=sourceWitnessInstances(machine,[law],before,goal,model,new Set(['sample']))
 expect(next).toBeDefined()
 expect(next?.[law.name]?.length).toBeGreaterThan(0)
 for(let i=0;i<(next?.[law.name]?.length??0);i+=3)expect(next![law.name]!.slice(i,i+3)).toContainEqual(x('sample'))
 expect(next?.untouched).toBe(before.untouched)
 expect(JSON.stringify(before)).toBe(saved)
 if(next){
  const refined={...goal,hyps:[...goal.hyps,...assumed([law],next)]},proof=grow(refined,new Map(),{nodes:0,until:clock()+1000})
  expect('tree'in proof).toBe(true)
  if('tree'in proof)expect(check(refined,proof.tree)).toBe(true)
  const again=sourceWitnessInstances(machine,[law],next,goal,model,new Set(['sample']))
  if(again){
   expect(again[law.name]!.slice(0,next[law.name]!.length)).toEqual(next[law.name]!)
   const tuples=Array.from({length:again[law.name]!.length/3},(_,i)=>JSON.stringify(again[law.name]!.slice(i*3,i*3+3)))
   expect(new Set(tuples).size).toBe(tuples.length)
   expect(again[law.name]!.length-next[law.name]!.length).toBeLessThanOrEqual(24)
  }
 }
})

test('source feedback requires a read witness and preserves count-key freshness',()=>{
 const {machine,law,goal,model}=fixture(),counted:Law={name:'count dependent',forall:'row',holds:same(get('Total',x('row')),n(0))}
 expect(sourceWitnessInstances(machine,[law],{},goal,model,new Set())).toBeUndefined()
 expect(sourceWitnessInstances(machine,[law],{},goal,model,new Set(['unrelated']))).toBeUndefined()
 const offered=sourceWitnessInstances(machine,[counted],{},goal,model,new Set(['sample']))
 expect(offered?.[counted.name]??[]).not.toContainEqual(x('sample'))
})
