import {expect,test} from 'bun:test'
import {type Law,type Machine,get,n,x} from './machine.ts'
import {countedAttempts,countsDump} from './counts.ts'
import {clock,counted,fullRate,withDeadline,withWall} from '../kernel/prove.ts'
import {checkMC,countedObligations} from '../kernel/kernel.ts'

test('count targets complete existing premises once before the first model query; fields stay lazy',()=>{
 const m:Machine={name:'completion order',params:[],inputs:[],state:{},maps:{Cells:0},counts:{Total:{j:'countRow',key:'member',below:n(2),body:get('Cells',x('member'))}},step:{}}
 const countLaw:Law={name:'bounded total',forall:'row',holds:{op:'<=',a:get('Total',x('row')),b:n(1)}}
 const fieldLaw:Law={name:'bounded field',forall:'row',holds:{op:'<=',a:get('Cells',x('row')),b:n(1)}}
 const prior=countsDump.on
 try{
  for(const law of [countLaw,fieldLaw]){
   const phases:string[]=[],sizes:number[]=[]
   countsDump.on=e=>{
    if('phase'in e&&typeof e.phase==='string'){
     phases.push(e.phase)
     if(e.phase==='count-completion'&&'added'in e&&Array.isArray(e.added))sizes.push(e.added.length)
    }
   }
   const result=withWall(performance.now()+3000,()=>counted(fullRate,()=>{
    const until=clock()+1000
    return withDeadline(until,()=>countedAttempts(m,[law],new Set(),until).traced(law,[law],1,1000))
   },true))
   // This universal count target is a scheduling probe, not a promised proof.
   // Keep the independently checked positive field path mandatory.
   if(law===fieldLaw)expect('proof'in result).toBe(true)
   if('proof'in result)for(const {goal,decls}of countedObligations(m,[law],{[law.name]:result.proof.instances},0))expect(checkMC(goal.hyps,decls,result.proof.certs[goal.name]!)).toBe(true)
   const first=phases.indexOf('query'),completion=phases.indexOf('count-completion')
   expect(first).toBeGreaterThanOrEqual(0)
   if(law===countLaw){expect(completion).toBeGreaterThanOrEqual(0);expect(completion).toBeLessThan(first);expect(sizes).toHaveLength(1);expect(sizes[0]).toBeLessThanOrEqual(48)}
   else expect(completion===-1||completion>first).toBe(true)
  }
 }finally{countsDump.on=prior}
})

test('a concrete-key count target retains an independently checked conditional certificate',()=>{
 const m:Machine={name:'concrete completion',params:[],inputs:[],state:{ready:n(0)},maps:{Cells:0},counts:{Total:{j:'countRow',key:'member',below:n(2),body:{op:'ite',c:{op:'=',a:get('Cells',x('member')),b:n(1)},yes:n(1),no:n(0)}}},step:{state:{ready:n(1)}}}
 const law:Law={name:'bounded target',holds:{op:'or',xs:[{op:'=',a:x('ready'),b:n(0)},{op:'<=',a:get('Total',n(0)),b:n(2)}]}},premise:Law={name:'bounded source',forall:'row',holds:{op:'<=',a:get('Total',x('row')),b:n(2)}},family=[law,premise]
 const result=withWall(performance.now()+3000,()=>counted(fullRate,()=>{const until=clock()+1000;return withDeadline(until,()=>countedAttempts(m,family,new Set(),until).traced(law,family,1,1000))},true))
 expect('proof'in result).toBe(true)
 if('proof'in result)for(const {goal,decls}of countedObligations(m,family,{[law.name]:result.proof.instances},0))expect(checkMC(goal.hyps,decls,result.proof.certs[goal.name]!)).toBe(true)
})

