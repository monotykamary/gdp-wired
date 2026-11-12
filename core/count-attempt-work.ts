// Finite per-round inventory, not a profiler. Physical leaf scopes all map to
// the ONE leaf allowance slot in 46.11. Case use includes nested leaf use;
// summing it again is conservative, never credit. The aggregate round cutoff
// remains authoritative for repeated and unkeyed work.
import {type LiftedWorkTraceEvent} from './count-lifted-budget.ts'
import {type CountRetryKey,type CountSlice} from './count-retry-budget.ts'
import {type WorkLedger,workLedger} from './work-admission.ts'
import {type WorkAmount,compareWork,workAdd,zeroWork} from './work-amount.ts'
export const countLeafSlot='leaf'
type Slot={key:string,allocation:WorkAmount,used:WorkAmount,completed:number,stopped:number}
type Active=CountSlice&{kind:'case'|'leaf',renewable:boolean}
export class CountAttemptWork{
 readonly slices:CountSlice[]=[]
 private slots=new Map<string,Slot>()
 private active=new Map<number,Active>()
 private failed:CountSlice|undefined
 private invalid=false
 private tick(site:string):void{this.bank.start('ticks',1,'count attempt '+site)}
 constructor(keys:readonly CountRetryKey[],private bank:WorkLedger=workLedger){
  this.tick('inventory header')
  if(!keys.length||keys.length>64)throw new RangeError('unbounded count attempt keys')
  for(const key of keys){
   this.tick('inventory key')
   if(!key.key||key.key.length>256||this.slots.has(key.key)||key.allocation.num<=0n||key.allocation.den<=0n)throw new RangeError('invalid count attempt key')
   this.slots.set(key.key,{...key,used:zeroWork,completed:0,stopped:0})
  }
 }
 trace=(event:LiftedWorkTraceEvent):void=>{
  this.tick('slice event')
  const slice=event.slice,key=slice.kind==='leaf'?countLeafSlot:slice.key,slot=this.slots.get(key)
  if(!slot||compareWork(slot.allocation,slice.allocation)!==0){this.invalid=true;this.slices.length=0;return}
  if(event.stage==='start'){
   if(this.active.has(slice.scopeId)||this.active.size>=64){this.invalid=true;this.slices.length=0;return}
   let parent:Active|undefined
   for(const active of this.active.values()){this.tick('slice parent');if(active.kind==='case')parent=active}
   if(slice.kind==='leaf'&&slice.caseKey!==undefined&&parent?.key!==slice.caseKey){this.invalid=true;this.slices.length=0;return}
   this.active.set(slice.scopeId,{...slice,key,physicalKey:slice.key,caseKey:parent?.key,renewable:slice.kind==='case'||!!parent})
  }else{
   const active=this.active.get(slice.scopeId)
   if(!this.active.delete(slice.scopeId)||event.used.num<0n){this.invalid=true;this.slices.length=0;return}
   slot.used=workAdd(slot.used,event.used)
   if(event.completed)slot.completed++;else{
    slot.stopped++
    const refusal=this.bank.capacityRefusal(event.error)
    if(active?.renewable&&refusal?.limiting.length===1&&refusal.limiting[0]!.id===slice.scopeId)this.failed=active
   }
  }
  this.slices.length=0
  if(this.invalid)return
  for(const active of this.active.values()){this.tick('active slice');if(active.renewable)this.slices.push(active)}
  if(this.failed&&!this.active.has(this.failed.scopeId))this.slices.push(this.failed)
 }
 keys():readonly CountRetryKey[]{
  const out:CountRetryKey[]=[]
  for(const {key,allocation,used}of this.slots.values()){this.tick('key snapshot');out.push({key,allocation,used})}
  return out
 }
 inventory():readonly Readonly<Slot&{unseen:boolean}>[]{
  const out:Array<Slot&{unseen:boolean}>=[]
  for(const slot of this.slots.values()){this.tick('inventory snapshot');out.push({...slot,unseen:slot.completed+slot.stopped===0})}
  return out
 }
 valid():boolean{return !this.invalid}
}
