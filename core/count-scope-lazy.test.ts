import {expect,test} from 'bun:test'
import {type Law,type Machine,atMost,less,min,n,x} from './machine.ts'
import {type CountCert,type Instances,checkMC,countedObligations,leafConstraints,mcGoal,termColumn} from '../kernel/kernel.ts'
import {withWall} from '../kernel/prove.ts'
import {type CountLawProof,type ScopedCountProof,replayScopedCountProof,resolveCountScopeSuppliers,scopeCountProof,scopeCountProofPair} from './count-proof-scope.ts'
import {rescopeCountProof} from './count-proof-rescope.ts'
import {CountRecipePass,runCountRecipeController} from './count-recipe-controller.ts'
import {BudgetExpired,WorkLedger,workLedger,withWorkAdmissionTrace} from './work-admission.ts'
import {workAmount,workShare,zeroWork} from './work-amount.ts'
import {type WorkKey,workKeys} from './work-kinds.ts'
import {completeWorkProfile} from './work-profile.ts'

function fixture(nested:boolean){
 const m:Machine={name:'lazy H0 H1 t',params:[],inputs:[],state:{x:n(0),y:n(0),z:n(0)},step:{state:{x:x('x'),y:x('y'),z:x('z')}}}
 const h0:Law={name:'H0',holds:less(x('x'),n(0))}
 const t=min(x('x'),x('y')),supplierTerm=nested?min(min(x('x'),x('k')),x('z')):min(x('x'),x('k'))
 const h1:Law={name:'H1',forall:'k',holds:atMost(supplierTerm,n(100))}
 const owner:Law={name:'target',holds:atMost(x('z'),n(10))},family=[h0,h1,owner]
 const instances:Instances={[h1.name]:[x('y')]},certs:Record<string,CountCert>={}
 for(const {goal,decls}of countedObligations(m,family,{[owner.name]:instances},2)){
  const base={reads:[],insts:[]},expanded=mcGoal(goal.hyps,decls,base)!,rows=leafConstraints(expanded,new Map())
  const find=(pred:(row:typeof rows[number])=>boolean)=>{const at=rows.findIndex(pred);if(at<0)throw Error('missing lazy control row: '+goal.name);return at}
  let cert:CountCert
  if(goal.name.endsWith(' @start')){
   const contradiction=find(row=>(row.lin['1']??0)>0&&Object.entries(row.lin).every(([key,value])=>key==='1'||value===0))
   cert={...base,tree:{leaf:[{kind:'input',index:contradiction}]}}
  }else{
   const name=termColumn(t),fact=find(row=>row.src!==undefined&&'fact'in row.src&&row.lin.x===1&&row.lin['1']===1)
   const term=find(row=>row.src!==undefined&&'term'in row.src&&row.src.term===name&&row.lin[name]===1&&row.lin.x===-1)
   const nat=find(row=>row.src!==undefined&&'nat'in row.src&&row.src.nat===name)
   cert={...base,tree:{leaf:[{kind:'input',index:fact},{kind:'input',index:term},{kind:'combine',a:0,b:1,ma:1,mb:1},{kind:'input',index:nat},{kind:'combine',a:2,b:3,ma:1,mb:1}]}}
  }
  expect(checkMC(goal.hyps,decls,cert)).toBe(true)
  certs[goal.name]=cert
 }
 const proof:CountLawProof={status:'unchecked',instances,certs}
 return {m,h0,h1,owner,family,proof}
}

// The original ten tests remain unchanged. This additional control runs the
// real legacy capture, full on-demand supplier helper, exact transport/native
// check, and the controller's bounded reclosure. H0's contradiction is a local
// source hypothesis, NOT a claim that the H0/H1 family is an inductive theorem.
test('lazy H0/H1/t: no eager supplier scan, retain instances, reclose once, fail closed',()=>withWall(performance.now()+30000,()=>{
 expect(completeWorkProfile.enabled).toBe(true)
 for(const nested of [false,true]){
  const f=fixture(nested),entries:string[]=[]
  const captured=withWorkAdmissionTrace(event=>{if(event.kind==='start'&&event.site==='pair-scope:entry')entries.push(event.site)},()=>
   rescopeCountProof(f.m,f.owner,f.family,f.proof,new Set(),Infinity,undefined,{retainUncheckedOffer:true}))!
  expect(captured).toBeDefined();expect(entries).toEqual([])
  expect(captured.suppliers).toBe('unresolved');expect(captured.proof.status).toBe('unchecked')
  expect(captured.premises.map(p=>p.name)).toEqual(['H0'])
  expect(captured.unused).toContain('H1');expect(captured.proof.instances).toBe(f.proof.instances)
  expect(captured.proof.certs).toBe(f.proof.certs);expect(captured.proof.instances.H1).toEqual([x('y')])
  // One scan yields byte-equivalent offered/inferred metadata, including when
  // a declared superset and unchecked status must be stripped from inference.
  const declared={...f.proof,premises:f.family.map(l=>l.name)},pair=scopeCountProofPair(f.m,f.owner,f.family,declared,Infinity)
  expect(JSON.stringify(pair.offered)).toBe(JSON.stringify(scopeCountProof(f.m,f.owner,f.family,declared,Infinity)))
  expect(JSON.stringify(pair.inferred)).toBe(JSON.stringify(scopeCountProof(f.m,f.owner,f.family,{instances:f.proof.instances,certs:f.proof.certs},Infinity)))

  for(const mode of ['success','missing-supplier','second-decline','repair-hard-stop'] as const){
   const b=new WorkLedger(Object.fromEntries(workKeys.map(key=>[key,1])) as Record<WorkKey,number>)
   b.withBudget(workAmount(1000000n),()=>{
    const pass=new CountRecipePass<ScopedCountProof|undefined>(f.family.map((law,reference)=>({name:law.name,reference,recipes:[{id:'done',kind:'ordinary',required:[]}]})),'fixed H0 H1 t',b)
    for(const state of pass.states){
     state.recipes[0]!.terminal=true
     if(state.member.name==='H1'&&mode==='missing-supplier')continue
     // Helpers are opaque bookkeeping payloads, not forged native receipts.
     state.held={recipeId:'done',payload:state.member.name==='target'?captured:undefined,premises:state.member.name==='target'?['H0']:[],checkedReduced:false,checkCost:zeroWork}
    }
    let pending:string|undefined,repairs=0,closes=0
    const seen:string[][]=[],marker=new BudgetExpired('lazy repair original hard stop')
    const hooks={
     construct:()=>{throw Error('lazy closing must not run a recipe')},
     declinedMember:()=>pending,
     repairSuppliers:(name:string,payload:ScopedCountProof|undefined)=>{
      repairs++;expect(name).toBe('target');expect(pass.supplierRepairUsed).toBe(true)
      if(mode==='repair-hard-stop')throw marker
      const repaired=resolveCountScopeSuppliers(f.m,f.family,payload!,Infinity)!
      expect(repaired).toBeDefined();expect(repaired.suppliers).toBe('resolved');expect(repaired.checkedReduced).toBeUndefined()
      expect(repaired.proof.status).toBe('unchecked');expect(repaired.proof.instances).toBe(f.proof.instances)
      expect(repaired.proof.certs).toBe(f.proof.certs);expect(repaired.sources).toBe(captured.sources)
      expect(repaired.premises.map(p=>p.name)).toEqual(['H0','H1']);expect(repaired.unused).not.toContain('H1')
      expect(resolveCountScopeSuppliers(f.m,f.family,repaired,Infinity)).toBeUndefined()
      return {payload:repaired,premises:repaired.premises.map(p=>p.name)}
     },
     close:(rows:readonly {id:string,payload:ScopedCountProof|undefined}[],targetInFamily:boolean)=>{
      closes++;pending=undefined;seen.push(rows.map(row=>row.id))
      const target=rows.find(row=>row.id==='target')
      if(!target)return false
      if(mode==='second-decline'&&closes>1){pending='target';return false}
      const family=f.family.filter(l=>rows.some(row=>row.id===l.name))
      const replayed=replayScopedCountProof(f.m,family,target.payload!,Infinity,{onTransportDecline:obligation=>{expect(obligation).toBe('target @step');pending='target'}})
      if(!replayed)return false
      expect(targetInFamily).toBe(true);expect(replayed.instances.H1).toEqual([x('y')])
      for(const {goal,decls}of countedObligations(f.m,family,{target:replayed.instances},family.findIndex(l=>l.name==='target')))
       expect(checkMC(goal.hyps,decls,replayed.certs[goal.name]!)).toBe(true)
      return true
     }
    }
    if(mode==='repair-hard-stop'){
     let error:unknown
     try{runCountRecipeController(pass,['target'],hooks)}catch(caught){error=caught}
     expect(error).toBe(marker);expect(repairs).toBe(1);expect(closes).toBe(1)
    }else{
     const result=runCountRecipeController(pass,['target'],hooks)
     expect(result.result).toBe(mode==='success');expect(repairs).toBe(1);expect(closes).toBe(2)
     expect(seen[0]).toEqual(['H0','target'])
     expect(seen[1]).toEqual(mode==='missing-supplier'?['H0']:['H0','H1','target'])
     expect(pass.held().get('target')!.premises).toEqual(['H0','H1'])
     if(mode==='second-decline'){
      runCountRecipeController(pass,['target'],hooks)
      expect(repairs).toBe(1) // a later invocation cannot renew the repair.
     }
    }
    expect(pass.supplierRepairUsed).toBe(true)
   })
  }
 }
 // B's reused boundary must preserve the original authenticated refusal even
 // when a nested native helper catches it; no new/fabricated BudgetExpired.
 let original:unknown,propagated:unknown
 workLedger.withBudget(workShare(workLedger.weights.ticks,1n,2n),()=>{
  try{workLedger.withCapacityRefusalBoundary(()=>{try{workLedger.start('ticks',1,'lazy swallowed hard stop')}catch(error){original=error}})}catch(error){propagated=error}
 })
 expect(propagated).toBe(original);expect(propagated).toBeInstanceOf(BudgetExpired)
 expect(workLedger.capacityRefusal(propagated)?.reason).toBe('quantum')
}))
