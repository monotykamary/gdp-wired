import {expect,test} from 'bun:test'
import {type Law,type Machine,get,n,same,x} from './machine.ts'
import {certFor} from './counts.ts'
import {finishCountStrategy} from './count-strategy.ts'
import {closingCountCheck,deferFinalCountStep,familyStepProposal,finalCountStepDeferralEnabled} from './count-final-step.ts'
import {type CountCert,type Instances,checkCountedLaws,checkMC,countedObligations,mcGoal} from '../kernel/kernel.ts'
import {clock,counted,fullRate,grow,rowsAt} from '../kernel/prove.ts'
import {solve} from './solver.ts'
import {scopeCountProof,replayScopedCountProof} from './count-proof-scope.ts'
const enabled=finalCountStepDeferralEnabled(), opt=enabled?test:test.skip
function fixture(){
 const m:Machine={name:'natural count proposal',params:[],inputs:[],state:{},maps:{tokens:0},step:{},counts:{total:{j:'row',key:'member',below:n(1),body:{op:'if',c:same(get('tokens',x('member')),n(1)),then:n(1),else:n(0)}}}}
 const law:Law={name:'natural count',forall:'r',holds:{op:'<=',a:n(0),b:get('total',x('r'))}}, family=[law],instances={[law.name]:[x('r#')]},until=clock()+10000
 const packets=countedObligations(m,family,{[law.name]:instances},0),step=packets.at(-1)!,request=certFor(step.goal,step.decls,false,0),goal=mcGoal(step.goal.hyps,step.decls,request)!,out=grow(goal,new Map(),{nodes:0,until})
 if(!('tree'in out))throw Error('fixture did not close')
 const cert:CountCert={...request,tree:out.tree}
 const finish=(candidate=cert,defer=false,events:string[]=[])=>finishCountStrategy(m,family,law,instances,'total',candidate,until,(g,ds)=>certFor(g,ds,false,0),(stage,checked)=>events.push(stage+':'+checked),defer?{familyProposal:familyStepProposal}:{})
 return {m,law,family,instances,until,finish,cert}
}
test('final STEP deferral needs the internal capability as well as full-mode opt-in',()=>{
 expect(deferFinalCountStep()).toBe(false);expect(deferFinalCountStep(familyStepProposal)).toBe(enabled)
})
test('standalone finishing remains checked even with the environment opt-in',()=>counted(fullRate,()=>{
 const f=fixture(),events:string[]=[],p=f.finish(f.cert,false,events)
 expect(p).toBeDefined();expect(p?.status).toBeUndefined();expect(events).toContain('step-check:true')
 if(p)expect(checkCountedLaws(f.m,f.family,{instances:{[f.law.name]:p.instances},certs:p.certs})).toBe(true)
},true))
opt('a bad deferred STEP is a proposal, never an accepted proof',()=>counted(fullRate,()=>{
 const f=fixture(),events:string[]=[],p=f.finish({...f.cert,tree:{leaf:[]}},true,events)
 expect(p?.status).toBe('unchecked');expect(events).toContain('step-proposal:false');expect(events.some(e=>e.startsWith('step-check:'))).toBe(false)
 expect(p).toBeDefined();if(!p)return
 let calls=0;expect(closingCountCheck(()=>{calls++;return checkCountedLaws(f.m,f.family,{instances:{[f.law.name]:p.instances},certs:p.certs})})).toBe(false);expect(calls).toBe(1)
},true))
opt('valid proposal checks current bytes each time, including a post-check mutation',()=>counted(fullRate,()=>{
 const f=fixture(),p=f.finish(f.cert,true)!;expect(p.status).toBe('unchecked')
 const packet={instances:{[f.law.name]:p.instances},certs:p.certs};let calls=0
 const close=()=>closingCountCheck(()=>{calls++;return checkCountedLaws(f.m,f.family,packet)})
 expect(close()).toBe(true);p.certs[f.law.name+' @step']!.tree={leaf:[]};expect(close()).toBe(false);expect(calls).toBe(2)
},true))
opt('closing refuses missing/bad INIT, bad STEP and malformed changed inputs',()=>counted(fullRate,()=>{
 const f=fixture(),p=f.finish(f.cert,true)!,proof={instances:{[f.law.name]:p.instances},certs:p.certs}
 const refused=(mutate:(m:Machine,q:typeof proof)=>void)=>{const m=structuredClone(f.m),q=structuredClone(proof);mutate(m,q);expect(closingCountCheck(()=>checkCountedLaws(m,f.family,q))).toBe(false)}
 refused((_m,q)=>{delete q.certs[f.law.name+' @start']})
 refused((_m,q)=>{q.certs[f.law.name+' @start']!.tree={leaf:[]}})
 refused((_m,q)=>{q.certs[f.law.name+' @step']!.tree={leaf:[]}})
 refused((m)=>{m.counts!.total!.below=n(2)})
 refused((_m,q)=>{q.certs[f.law.name+' @step']!.reads[0]![1]='missing count declaration'})
},true))
opt('a deferred replay remains unchecked; standalone replay still checks',()=>counted(fullRate,()=>{
 const f=fixture(),p=f.finish(f.cert,true)!,scoped=scopeCountProof(f.m,f.law,f.family,p,f.until)!
 expect(scoped).toBeDefined()
 const proposed=replayScopedCountProof(f.m,f.family,scoped,f.until,{deferToClosing:true})
 expect(proposed?.status).toBe('unchecked');if(!proposed)return
 proposed.certs[f.law.name+' @step']!.tree={leaf:[]}
 expect(closingCountCheck(()=>checkCountedLaws(f.m,f.family,{instances:{[f.law.name]:proposed.instances},certs:proposed.certs}))).toBe(false)
 p.certs[f.law.name+' @step']!.tree={leaf:[]}
 expect(replayScopedCountProof(f.m,f.family,scoped,f.until)).toBeUndefined()
},true))
opt('a deferred proposal cannot use a dropped or changed helper',()=>counted(fullRate,()=>{
 const m:Machine={name:'dependent proposal',params:[],inputs:[],state:{left:n(0),right:n(0)},step:{state:{left:x('right'),right:x('left')}}}
 const left:Law={name:'left',holds:same(x('left'),n(0))},right:Law={name:'right',holds:same(x('right'),n(0))},family=[left,right],until=clock()+10000,certs:Record<string,CountCert>={}
 for(const {goal,decls}of countedObligations(m,family,{left:{}},0)){
  const request={reads:[],insts:[]},expanded=mcGoal(goal.hyps,decls,request)!,result=grow(expanded,new Map(),{nodes:0,until})
  if(!('tree'in result))throw Error('dependent fixture did not close');certs[goal.name]={...request,tree:result.tree}
 }
 const scoped=scopeCountProof(m,left,family,{instances:{},certs,status:'unchecked'},until)!
 expect(scoped.premises.map(p=>p.name)).toContain('right')
 expect(replayScopedCountProof(m,[left],scoped,until,{deferToClosing:true})).toBeUndefined()
 expect(replayScopedCountProof(m,[left,{...right,holds:same(x('right'),n(1))}],scoped,until,{deferToClosing:true})).toBeUndefined()
},true))
opt('the closing gate enforces global witness freshness beyond per-packet validity',()=>counted(fullRate,()=>{
 const m:Machine={name:'closing freshness',params:['collision'],inputs:[],state:{},counts:{C:{j:'row',key:'k',below:n(1),body:n(0)}},step:{}}
 const law:Law={name:'constant',holds:same(n(0),n(0))},instances={[law.name]:{}},packets=countedObligations(m,[law],instances),certs:Record<string,CountCert>={}
 for(const p of packets){
  const request={reads:[['r',p.decls[0]!.map,n(0)] as [string,string,ReturnType<typeof n>]],insts:[{wit:'safe',below:n(1),terms:[[1,'r'] as [number,string]],unit:0}],picks:[]},goal=mcGoal(p.goal.hyps,p.decls,request)!,result=solve(rowsAt(goal,new Map()),500)
  if(result.kind!=='refuted')throw Error('freshness fixture did not close');certs[p.goal.name]={...request,tree:{leaf:result.steps}}
 }
 expect(closingCountCheck(()=>checkCountedLaws(m,[law],{instances,certs}))).toBe(true)
 const collided=Object.fromEntries(Object.entries(certs).map(([name,c])=>[name,{...c,insts:c.insts.map(i=>({...i,wit:'collision'}))}]))
 expect(packets.every(p=>checkMC(p.goal.hyps,p.decls,collided[p.goal.name]!))).toBe(true)
 expect(closingCountCheck(()=>checkCountedLaws(m,[law],{instances,certs:collided}))).toBe(false)
},true))

opt('changing a required helper instance invalidates the final family proposal',()=>counted(fullRate,()=>{
 const m:Machine={name:'instance-sensitive proposal',params:[],inputs:[],state:{left:n(0),right:n(0)},step:{state:{left:x('right'),right:x('right')}}}
 const target:Law={name:'left is zero',holds:same(x('left'),n(0))},helper:Law={name:'right is below each key',forall:'k',holds:{op:'<=',a:x('right'),b:x('k')}},family=[target,helper],until=clock()+10000
 const prove=(owner:Law,instances:Instances)=>{
  const certs:Record<string,CountCert>={}
  for(const {goal,decls}of countedObligations(m,family,{[owner.name]:instances},family.indexOf(owner))){
   const base={reads:[],insts:[]},expanded=mcGoal(goal.hyps,decls,base)!,out=grow(expanded,new Map(),{nodes:0,until})
   if(!('tree'in out))throw Error('instance fixture did not close');certs[goal.name]={...base,tree:out.tree}
  }
  return {instances,certs,status:'unchecked' as const}
 }
 const targetProof=prove(target,{[helper.name]:[n(0)]}),helperProof=prove(helper,{[helper.name]:[x('k#')]})
 const proof={instances:{[target.name]:targetProof.instances,[helper.name]:helperProof.instances},certs:{...targetProof.certs,...helperProof.certs}}
 expect(closingCountCheck(()=>checkCountedLaws(m,family,proof))).toBe(true)
 proof.instances[target.name]![helper.name]=[n(1)]
 expect(closingCountCheck(()=>checkCountedLaws(m,family,proof))).toBe(false)
},true))

opt('throwing and expired closing checks are clean refusals',()=>{
 expect(closingCountCheck(()=>{throw Error('malformed proposal')})).toBe(false)
 expect(closingCountCheck(()=>{throw Error('work budget expired')})).toBe(false)
})
