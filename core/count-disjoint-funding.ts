// Section46.17 NEXT-PIN API ONLY: not selected by the production controller.
// The interim production policy remains planCountRetry with the narrow cap fix.
// Callers must split their callback into explicit body/case segments; this API
// neither suspends ledger endpoints nor attributes work merely by its label.
import {BudgetExpired,type WorkLedger,workLedger} from './work-admission.ts'
import {type WorkAmount,compareWork,workAdd,workShare,workSub,zeroWork} from './work-amount.ts'
import {CountAttemptTickets,countAttemptStop,type CountAttemptStop,type CountSlice} from './count-retry-budget.ts'
import {type CountRoundValue,type CountRoundResult} from './count-retry-round.ts'
export type CountFundingCaps=Readonly<{cases:ReadonlyMap<string,WorkAmount>,leaf:WorkAmount}>
export type CountBodyHistory=Readonly<{completed:boolean,used:WorkAmount,instance:CountAttemptTickets,rootEpoch:number}>
export type CountDisjointContext=Readonly<{instance:CountAttemptTickets,bank:WorkLedger,parentId:number,parentEpoch:number,started:number}>
// Identity metadata only: this never grants work or creates a ticket.
export function countDisjointContext(instance:CountAttemptTickets,bank:WorkLedger=workLedger):CountDisjointContext{
 const parent=bank.currentScope()
 if(!parent||!bank.inBudget())throw Error('disjoint count context needs an existing root')
 return Object.freeze({instance,bank,parentId:parent.id,parentEpoch:bank.snapshot().scopeEpoch,started:instance.snapshot().started})
}
function sameContext(context:CountDisjointContext,instance:CountAttemptTickets,bank:WorkLedger):boolean{
 return context.instance===instance&&context.bank===bank&&context.started===instance.snapshot().started
  &&context.parentId===bank.currentScope()?.id&&context.parentEpoch===bank.snapshot().scopeEpoch
}
export type CountDisjointPlan=Readonly<{kind:'admitted',caps:CountFundingCaps,body:WorkAmount,minimumBody:WorkAmount,need:WorkAmount,rootEpoch:number,context:CountDisjointContext}>|
 Readonly<{kind:'refused',reason:'tickets'|'root'|'headroom'|'parent'|'stop'|'inventory'}>
const limit=1n<<4096n
const valid=(n:WorkAmount)=>n.den>0n&&n.num>=0n&&n.den<=limit&&n.num<=limit
export function planDisjointCountRound(caps:CountFundingCaps,body0:WorkAmount,history:readonly CountBodyHistory[],tickets:CountAttemptTickets,
 stop?:CountAttemptStop&{caseKey?:string},bank:WorkLedger=workLedger):CountDisjointPlan{
 bank.start('ticks',1,'disjoint count plan header')
 if(!bank.inBudget())return {kind:'refused',reason:'root'}
 if(tickets.snapshot().terminal||tickets.snapshot().remaining===0)return {kind:'refused',reason:'tickets'}
 if(!caps.cases.size||caps.cases.size>63||history.length>7||!valid(caps.leaf)||caps.leaf.num===0n||!valid(body0))return {kind:'refused',reason:'inventory'}
 const cases=new Map<string,WorkAmount>();let leaf=caps.leaf,total=zeroWork,minimumBody=body0
 if(stop&&stop.kind!=='soft-slice')return {kind:'refused',reason:'stop'}
 if(stop&&stop.rootEpoch!==bank.snapshot().rootEpoch)return {kind:'refused',reason:'root'}
 let found=!stop
 for(const [key,cap]of caps.cases){
  bank.start('ticks',1,'disjoint count case validation')
  if(!key||key.length>256||key==='leaf'||key==='body'||!valid(cap)||cap.num===0n)return {kind:'refused',reason:'inventory'}
  if(stop?.key===key){if(compareWork(stop.allocation,cap)!==0)return {kind:'refused',reason:'stop'};found=true}
  const next=stop?.key===key?workShare(cap,2n,1n):cap
  cases.set(key,next);total=workAdd(total,next)
 }
 if(stop?.key==='leaf'){
  if(compareWork(stop.allocation,leaf)!==0||!stop.caseKey||!cases.has(stop.caseKey))return {kind:'refused',reason:'parent'}
  leaf=workShare(leaf,2n,1n)
  if(compareWork(leaf,cases.get(stop.caseKey)!)>0)return {kind:'refused',reason:'parent'}
  found=true
 }
 if(!found)return {kind:'refused',reason:'stop'}
 let completed=false
 for(const entry of history){
  bank.start('ticks',1,'disjoint count body history')
  if(!valid(entry.used)||entry.instance!==tickets||entry.rootEpoch!==bank.snapshot().rootEpoch)return {kind:'refused',reason:'inventory'}
  if(entry.completed&&(!completed||compareWork(entry.used,minimumBody)>0)){minimumBody=entry.used;completed=true}
 }
 // Read H only after every paid preparation step. It already intersects every
 // live ancestor and outstanding reservation; no caller-supplied H is trusted.
 const headroom=bank.available()
 if(headroom===null)return {kind:'refused',reason:'root'}
 if(compareWork(workAdd(total,minimumBody),headroom)>0)return {kind:'refused',reason:'headroom'}
 return Object.freeze({kind:'admitted',caps:{cases,leaf},body:workSub(headroom,total),minimumBody,need:headroom,rootEpoch:bank.snapshot().rootEpoch,context:countDisjointContext(tickets,bank)})
}
export type CountOwnerReceipt=Readonly<{body:WorkAmount,cases:ReadonlyMap<string,WorkAmount>,sum:WorkAmount,round:WorkAmount,complete:boolean}>
export class CountFundingOwners{
 private failedSlice:CountSlice|undefined
 get slices():readonly CountSlice[]{return this.failedSlice?[this.failedSlice]:[]}
 private active:Readonly<{kind:'body'|'case',key:string,start:WorkAmount}>|undefined
 private ending=false
 private settling=false
 private bodyUse=zeroWork
 private caseUse=new Map<string,WorkAmount>()
 private ownerUse=zeroWork
 private finished:CountOwnerReceipt|undefined
 private readonly start:WorkAmount
 constructor(private plan:Extract<CountDisjointPlan,{kind:'admitted'}>,private bank:WorkLedger=workLedger,private completion:WorkAmount=zeroWork){this.start=bank.actual()}
 ownsBank(bank:WorkLedger):boolean{return this.bank===bank}
 body<T>(run:()=>T):T{return this.segment('body','body',workSub(this.plan.body,this.completion),run)}
 // The runner reserves this tail inside the SAME body cap before user work.
 // No case credit or new allowance can pay settlement after an interruption.
 settle<T>(run:()=>T):T{
  if(this.ending||this.active)throw new BudgetExpired('duplicate disjoint settlement')
  this.ending=true;this.settling=true
  try{return this.segment('body','body',this.plan.body,run)}finally{this.settling=false}
 }
 checkCoverage():void{
  const now=this.bank.actual(),live=this.active?workSub(now,this.active.start):zeroWork
  if(compareWork(workAdd(this.ownerUse,live),workSub(now,this.start))!==0)throw new BudgetExpired('unowned or overlapping count round work')
 }
 case<T>(key:string,run:()=>T):T{
  const cap=this.plan.caps.cases.get(key)
  if(!cap)throw new BudgetExpired('unknown disjoint count case')
  return this.segment('case',key,cap,run)
 }
 private segment<T>(kind:'body'|'case',key:string,cap:WorkAmount,run:()=>T):T{
  if(this.finished||this.ending&&!this.settling)throw new BudgetExpired('closed disjoint count owners')
  if(this.active)throw new BudgetExpired('overlapping disjoint count owners')
  const used=kind==='body'?this.bodyUse:this.caseUse.get(key)??zeroWork,left=workSub(cap,used),before=this.bank.actual()
  if(compareWork(left,zeroWork)<0)throw new BudgetExpired('spent disjoint count owner')
  try{return this.bank.withBudget(left,()=>{
   this.active={kind,key,start:before}
   const scope=this.bank.currentScope()!,slice={key,allocation:cap,scopeId:scope.id,rootEpoch:this.plan.rootEpoch}
   try{
    this.bank.start('ticks',1,'disjoint count owner bookkeeping')
    return run()
   }catch(error){this.retainFailure(error,slice,kind==='case');throw error}
   finally{this.active=undefined}
  })}finally{
   const amount=workSub(this.bank.actual(),before)
   this.ownerUse=workAdd(this.ownerUse,amount)
   if(kind==='body')this.bodyUse=workAdd(this.bodyUse,amount);else this.caseUse.set(key,workAdd(used,amount))
  }
 }
 leaf<T>(physicalKey:string,run:()=>T,expectedCase?:string):T{
  const owner=this.active
  if(this.finished)throw new BudgetExpired('closed disjoint count owners')
  if(!owner)throw new BudgetExpired('unowned count leaf')
  if(expectedCase!==undefined&&(owner.kind!=='case'||owner.key!==expectedCase))throw new BudgetExpired('mismatched count leaf owner')
  return this.bank.withBudget(this.plan.caps.leaf,()=>{
   const scope=this.bank.currentScope()!,slice={key:'leaf',allocation:this.plan.caps.leaf,scopeId:scope.id,rootEpoch:this.plan.rootEpoch,caseKey:owner.kind==='case'?owner.key:undefined,physicalKey}
   try{this.bank.start('ticks',1,'disjoint count leaf bookkeeping');return run()}
   catch(error){this.retainFailure(error,slice,owner.kind==='case');throw error}
  })
 }
 private retainFailure(error:unknown,slice:CountSlice,renewable:boolean):void{
  const refusal=this.bank.capacityRefusal(error)
  if(renewable&&refusal?.limiting.length===1&&refusal.limiting[0]!.id===slice.scopeId){this.failedSlice=slice}
 }
 receipt(complete:boolean):CountOwnerReceipt{
  if(this.finished)return this.finished
  if(this.active)throw new BudgetExpired('live disjoint owner at return')
  const round=workSub(this.bank.actual(),this.start)
  if(compareWork(this.ownerUse,round)!==0)throw new BudgetExpired('unowned or overlapping count round work')
  // No traversal/copy is hidden at an exhausted owner boundary. The private
  // map is exposed as a read-only final view; all subsequent segments refuse.
  return this.finished=Object.freeze({body:this.bodyUse,cases:this.caseUse,sum:this.ownerUse,round,complete})
 }
}
export function runDisjointCountRound<T>(plan:CountDisjointPlan,tickets:CountAttemptTickets,run:(owners:CountFundingOwners)=>CountRoundValue<T>,
 bank:WorkLedger=workLedger,eligible?:()=>boolean):Readonly<{result:CountRoundResult<T>,receipt?:CountOwnerReceipt}>{
 if(plan.kind==='refused')return {result:{kind:'not-started',reason:plan.reason}}
 if(!bank.inBudget()||plan.rootEpoch!==bank.snapshot().rootEpoch)return {result:{kind:'not-started',reason:'missing-root'}}
 if(!sameContext(plan.context,tickets,bank))return {result:{kind:'not-started',reason:'context'}}
 if(tickets.snapshot().terminal||tickets.snapshot().active)return {result:{kind:'not-started',reason:'tickets'}}
 // One terminal owner-entry tick and three fixed control operations: stop/
 // coverage classification, ticket settlement, and final receipt preparation.
 const completion=workShare(bank.weights.ticks,4n,1n)
 try{bank.checkAmount(plan.need,'disjoint count atomic admission')}catch(error){if(error instanceof BudgetExpired)return {result:{kind:'not-started',reason:'headroom'}};throw error}
 return bank.withBudget(plan.need,()=>{
  const owners=new CountFundingOwners(plan,bank,completion)
  let started=false,failed=false,failure:unknown,refusal:string|undefined,value:CountRoundValue<T>|undefined
  try{
   refusal=owners.body(()=>{
    const active=countDisjointContext(tickets,bank)
    if(eligible&&!eligible())return 'ineligible'
    if(!sameContext(active,tickets,bank)||active.started!==plan.context.started)return 'context'
    if(tickets.snapshot().terminal||tickets.snapshot().active)return 'tickets'
    bank.start('ticks',1,'disjoint count ticket');started=tickets.start()
    return started?undefined:'tickets'
   })
   if(!refusal)value=run(owners)
  }catch(error){failed=true;failure=error}
  let result:CountRoundResult<T>={kind:'not-started',reason:'precommit'}
  try{
   owners.settle(()=>{
    bank.start('ticks',1,'disjoint terminal classification')
    try{owners.checkCoverage()}catch(error){failed=true;failure=error}
    if(failed){
     const stop=countAttemptStop(failure,owners.slices,bank)
     result=!started?{kind:'not-started',reason:'precommit'}:stop.kind==='soft-slice'?{kind:'unfinished',stop}:{kind:'hard-cap',stop}
    }else result=refusal?{kind:'not-started',reason:refusal}:value!
    bank.start('ticks',1,'disjoint terminal ticket')
    if(started)tickets.finish(result.kind==='proposal'||result.kind==='decline'?result.kind:result.kind==='unfinished'?'unfinished':'hard-cap')
    bank.start('ticks',1,'disjoint terminal receipt')
   })
  }catch(error){
   // If even the reserved tail cannot run (e.g. unowned work spent its credit),
   // do not invent a free cleanup allowance. An active ticket stays unusable.
   if(!(error instanceof BudgetExpired))throw error
   return {result:{kind:'hard-cap',stop:{kind:'hard-cap',reason:'unclassified',error}}}
  }
  let receipt:CountOwnerReceipt|undefined
  try{receipt=owners.receipt(!failed&&!refusal)}catch(error){
   failed=true;failure=error;result={kind:'hard-cap',stop:{kind:'hard-cap',reason:'unclassified',error}}
  }
  if(failed&&!(failure instanceof BudgetExpired))throw failure
  return {result,receipt}
 })
}
