import {expect,test} from 'bun:test'
import {type Law,type Machine,get,n,x,ite,same} from './machine.ts'
import {countedAttempts,countsDump} from './counts.ts'
import {clock,counted,fullRate,withDeadline,withWall} from '../kernel/prove.ts'
import {checkMC,countedObligations} from '../kernel/kernel.ts'

test('count completion precedes the first query only for requested count maps, without proving a false INIT',()=>{
 const m:Machine={name:'completion order',params:[],inputs:[],state:{},maps:{Cells:0},counts:{Total:{j:'countRow',key:'member',below:n(2),body:n(1)},Other:{j:'otherRow',key:'otherMember',below:n(2),body:n(0)}},step:{}}
 const countLaw:Law={name:'bounded total',forall:'row',holds:{op:'<=',a:get('Total',x('row')),b:n(1)}}
 const fieldLaw:Law={name:'bounded field',forall:'row',holds:{op:'<=',a:get('Cells',x('row')),b:n(1)}}
 const unrelated:Law={name:'unrelated count',forall:'row',holds:{op:'<=',a:get('Other',x('row')),b:n(0)}}
 const prior=countsDump.on
 try{
  for(const law of [countLaw,fieldLaw]){
   const phases:string[]=[],sizes:number[]=[],completedNames:string[]=[]
   const laws=[law,unrelated]
   countsDump.on=e=>{
    if('phase'in e&&typeof e.phase==='string'){
     phases.push(e.phase)
     if(e.phase==='count-completion'&&'added'in e&&Array.isArray(e.added)){sizes.push(e.added.length);completedNames.push(...e.added.map((a:{law:string})=>a.law))}
    }
   }
   const result=withWall(performance.now()+3000,()=>counted(fullRate,()=>{
    const until=clock()+1000
    return withDeadline(until,()=>countedAttempts(m,[law],new Set(),until).traced(law,laws,1,1000))
   },true))
   // Total is always 2: its assumed bound cannot discharge the false INIT.
   expect('proof'in result).toBe(law===fieldLaw)
   if('proof'in result)for(const {goal,decls}of countedObligations(m,laws,{[law.name]:result.proof.instances},0))expect(checkMC(goal.hyps,decls,result.proof.certs[goal.name]!)).toBe(true)
   const first=phases.indexOf('query'),completion=phases.indexOf('count-completion')
   expect(first).toBeGreaterThanOrEqual(0)
   if(law===countLaw){expect(completion).toBeGreaterThanOrEqual(0);expect(completion).toBeLessThan(first);expect(sizes).toHaveLength(1);expect(sizes[0]).toBeLessThanOrEqual(48)}
   else expect(completion).toBe(-1)
   expect(completedNames).not.toContain(unrelated.name)
  }
 }finally{countsDump.on=prior}
})

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
 const m:Machine={name:'concrete completion',params:[],inputs:[],state:{ready:n(0)},maps:{Cells:0},counts:{Total:{j:'countRow',key:'member',below:n(2),body:ite(same(get('Cells',x('member')),n(1)),n(1),n(0))}},step:{state:{ready:n(1)}}}
 const law:Law={name:'bounded target',holds:{op:'or',xs:[same(x('ready'),n(0)),{op:'<=',a:get('Total',n(0)),b:n(2)}]}},premise:Law={name:'bounded source',forall:'row',holds:{op:'<=',a:get('Total',x('row')),b:n(2)}},family=[law,premise]
 const result=withWall(performance.now()+3000,()=>counted(fullRate,()=>{const until=clock()+1000;return withDeadline(until,()=>countedAttempts(m,family,new Set(),until).traced(law,family,1,1000))},true))
 expect('proof'in result).toBe(true)
 if('proof'in result)for(const {goal,decls}of countedObligations(m,family,{[law.name]:result.proof.instances},0))expect(checkMC(goal.hyps,decls,result.proof.certs[goal.name]!)).toBe(true)
})

