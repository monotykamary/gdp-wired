// Section46 admission metadata, not proof authority. The inventory is fixed per
// pass; no result can mint another recipe instance or replenish its tickets.
import {type WorkLedger,workLedger} from './work-admission.ts'
import {type WorkAmount,compareWork,workAdd,workAmount,workShare} from './work-amount.ts'
export const countRetryFuel=6
export type CountAttemptResult='unfinished'|'proposal'|'decline'|'hard-cap'
export class CountAttemptTickets {
 private left:number
 private active=false
 private ended=false
 private runs=0
 constructor(retries=countRetryFuel){
  if(!Number.isSafeInteger(retries)||retries<0||retries>countRetryFuel)throw new RangeError('invalid retry fuel')
  this.left=retries+1
 }
 start():boolean{
  if(this.active||this.ended||this.left===0)return false
  this.left--;this.runs++;this.active=true;return true
 }
 finish(result:CountAttemptResult):void{
  if(!this.active)throw new Error('attempt result without a started ticket')
  this.active=false
  if(result!=='unfinished'||this.left===0)this.ended=true
 }
 snapshot():Readonly<{remaining:number,started:number,active:boolean,terminal:boolean}>{
  return Object.freeze({remaining:this.left,started:this.runs,active:this.active,terminal:this.ended})
 }
}
export type CountSlice=Readonly<{key:string,allocation:WorkAmount,scopeId:number,rootEpoch:number}>
export type CountAttemptStop=Readonly<{kind:'soft-slice',key:string,allocation:WorkAmount,scopeId:number,rootEpoch:number}>|
 Readonly<{kind:'hard-cap',reason:'unclassified'|'enclosing-limit'|'scope-entry',error:unknown}>
export function countAttemptStop(error:unknown,slices:readonly CountSlice[],bank:WorkLedger=workLedger):CountAttemptStop{
 if(slices.length>64||!bank.inBudget())return {kind:'hard-cap',reason:'unclassified',error}
 const refusal=bank.capacityRefusal(error)
 if(!refusal)return {kind:'hard-cap',reason:'unclassified',error}
 if(refusal.reason==='scope-entry')return {kind:'hard-cap',reason:'scope-entry',error}
 // An equally limiting enclosing scope wins over a soft slice. Never infer a
 // slice from phase text, a clock subtraction, or the last event observed.
 if(refusal.limiting.length===1&&refusal.limiting[0]!.kind==='scope'){
  const rootEpoch=bank.snapshot().rootEpoch
  const matches=slices.filter(slice=>slice.scopeId===refusal.limiting[0]!.id&&slice.rootEpoch===rootEpoch)
  if(matches.length===1&&validAmount(matches[0]!.allocation,true)){
   const slice=matches[0]!;return {kind:'soft-slice',key:slice.key,allocation:slice.allocation,scopeId:slice.scopeId,rootEpoch:slice.rootEpoch}
  }
 }
 return {kind:'hard-cap',reason:'enclosing-limit',error}
}
export type CountRetryKey=Readonly<{key:string,allocation:WorkAmount,used:WorkAmount}>
export type CountRetryHeadroom=Readonly<{scope:string,remaining:WorkAmount}>
export type CountRetryPlan=Readonly<{kind:'admitted',need:WorkAmount,keys:readonly CountRetryKey[],rootEpoch:number}>|
 Readonly<{kind:'refused',reason:'hard-cap'|'unknown-key'|'changed-slice'|'headroom'|'missing-root',scope?:string,need?:WorkAmount}>
const numericLimit=1n<<4096n
const validAmount=(a:WorkAmount,positive=false)=>a.den>0n&&a.den<=numericLimit&&a.num<=numericLimit&&(positive?a.num>0n:a.num>=0n)
export function planCountRetry(keys:readonly CountRetryKey[],stop:CountAttemptStop,headrooms:readonly CountRetryHeadroom[],bank:WorkLedger=workLedger):CountRetryPlan{
 // Preparation is paid separately, before the atomic admission decision.
 // Refusing a prepared round starts no strategy body or ticket.
 bank.start('ticks',1,'count retry metadata header')
 if(keys.length===0||keys.length>64||headrooms.length>64)throw new RangeError('unbounded retry metadata')
 const names=new Set<string>()
 for(let i=0;i<keys.length;i++){
  bank.start('ticks',1,'count retry key validation');const key=keys[i]!
  if(!key.key||key.key.length>256||names.has(key.key)||!validAmount(key.allocation,true)||!validAmount(key.used))throw new RangeError('invalid retry key')
  names.add(key.key)
 }
 for(let i=0;i<headrooms.length;i++){
  bank.start('ticks',1,'count retry ancestor validation')
  if(!validAmount(headrooms[i]!.remaining))throw new RangeError('invalid retry headroom')
 }
 if(stop.kind!=='soft-slice')return {kind:'refused',reason:'hard-cap'}
 let raised:CountRetryKey|undefined
 for(let i=0;i<keys.length;i++){bank.start('ticks',1,'count retry key selection');if(keys[i]!.key===stop.key)raised=keys[i]}
 if(!raised)return {kind:'refused',reason:'unknown-key'}
 if(compareWork(raised.allocation,stop.allocation)!==0)return {kind:'refused',reason:'changed-slice'}
 const next:CountRetryKey[]=[];let need=workAmount(0n)
 for(let i=0;i<keys.length;i++){
  bank.start('ticks',1,'count retry allowance preparation');const key=keys[i]!
  const allocation=key===raised?workShare(key.allocation,2n,1n):compareWork(key.allocation,key.used)<0?key.used:key.allocation
  next.push(Object.freeze({key:key.key,allocation,used:workAmount(0n)}));need=workAdd(need,allocation)
 }
 const live=bank.available()
 if(live===null||!bank.inBudget()||stop.rootEpoch!==bank.snapshot().rootEpoch)return {kind:'refused',reason:'missing-root',need}
 for(let i=0;i<headrooms.length;i++){
  bank.start('ticks',1,'count retry ancestor comparison');const boundary=headrooms[i]!
  if(compareWork(need,boundary.remaining)>0)return {kind:'refused',reason:'headroom',scope:boundary.scope,need}
 }
 const remaining=bank.available()!
 if(compareWork(need,remaining)>0)return {kind:'refused',reason:'headroom',scope:'effective-ledger',need}
 return Object.freeze({kind:'admitted',need,keys:Object.freeze(next),rootEpoch:stop.rootEpoch})
}
