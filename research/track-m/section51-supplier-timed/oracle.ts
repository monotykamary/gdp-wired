import assert from 'node:assert/strict'

export type ExactRaw=Readonly<{numerator:string;denominator:string}>
export interface Snapshot {
 version:'strict-work-v1';rootEpoch:number;scopeEpoch:number;counterEpoch:number
 actual:ExactRaw;reserved:ExactRaw;effectiveEnd:ExactRaw|null
 activeEndpoints:readonly Readonly<{id:number;kind:'root'|'scope'|'work-cap'|'deadline';end:ExactRaw}>[]
 weights:Readonly<Record<string,ExactRaw>>
 rootBaseline:Readonly<{actual:ExactRaw;counters:Readonly<Record<string,string>>}>|null
 counters:Readonly<Record<string,string>>
}
export interface Event extends Snapshot {
 sequence:number;kind:'trace-start'|'trace-end'|'reserve'|'start'|'release'|'invalidate'|'refuse'|'scope-enter'|'scope-exit'
 sink?:string;site?:string;requested?:string;granted?:string;leaseId?:number
}
type Q={n:bigint;d:bigint}
export class PrefixViolation extends Error {constructor(message:string){super(message);this.name='PrefixViolation'}}
const need=(ok:boolean,message:string):void=>{if(!ok)throw new PrefixViolation(message)}
function integer(value:unknown):bigint {need(typeof value==='string'&&/^(0|[1-9][0-9]*)$/.test(value),'noncanonical nonnegative integer');return BigInt(value as string)}
function q(value:ExactRaw):Q {need(value!==null&&typeof value==='object','missing exact value');const n=integer(value.numerator),d=integer(value.denominator);need(d>0n,'zero denominator');return {n,d}}
const add=(a:Q,b:Q):Q=>({n:a.n*b.d+b.n*a.d,d:a.d*b.d})
const sub=(a:Q,b:Q):Q=>({n:a.n*b.d-b.n*a.d,d:a.d*b.d})
const cmp=(a:Q,b:Q)=>a.n*b.d-b.n*a.d
const zero:Q={n:0n,d:1n}
export function exactNumber(value:number):ExactRaw {
 assert(Number.isFinite(value)&&value>=0&&!Object.is(value,-0),'finite nonnegative IEEE value required')
 if(value===0)return {numerator:'0',denominator:'1'}
 const bits=new DataView(new ArrayBuffer(8));bits.setFloat64(0,value,false);const word=bits.getBigUint64(0,false)
 const exponent=Number((word>>52n)&2047n),fraction=word&((1n<<52n)-1n),significand=exponent===0?fraction:(1n<<52n)|fraction,shift=(exponent===0?-1022:exponent-1023)-52
 return shift>=0?{numerator:String(significand<<BigInt(shift)),denominator:'1'}:{numerator:String(significand),denominator:String(1n<<BigInt(-shift))}
}
export class PrefixOracle {
 private readonly baseline:Snapshot
 private previous:Snapshot
 private sequence:number|undefined
 readonly kinds=new Set<Event['kind']>()
 readonly sites=new Set<string>()
 events=0
 constructor(baseline:Snapshot){this.baseline=structuredClone(baseline);this.previous=this.baseline;this.check(baseline)}
 private check(snapshot:Snapshot):void {
  need(snapshot.version==='strict-work-v1','wrong meter version')
  for(const epoch of [snapshot.rootEpoch,snapshot.scopeEpoch,snapshot.counterEpoch])need(Number.isSafeInteger(epoch)&&epoch>=0,'invalid epoch')
  need(snapshot.rootEpoch===this.baseline.rootEpoch,'root changed within case')
  need(snapshot.scopeEpoch>=this.previous.scopeEpoch&&snapshot.counterEpoch>=this.previous.counterEpoch,'epoch rollback')
  const actual=q(snapshot.actual),reserved=q(snapshot.reserved),prices=this.baseline.weights,base=this.baseline.rootBaseline
  need(base!==null,'missing root baseline')
  need(cmp(actual,q(this.previous.actual))>=0n,'consumed work refunded')
  const keys=Object.keys(prices).sort();need(keys.length===26,'exactly 26 priced counters required')
  need(JSON.stringify(Object.keys(snapshot.counters).sort())===JSON.stringify(keys),'counter vector mismatch')
  need(JSON.stringify(Object.keys(base!.counters).sort())===JSON.stringify(keys),'root baseline counter vector mismatch')
  need(snapshot.rootBaseline!==null&&cmp(q(snapshot.rootBaseline.actual),q(base!.actual))===0n,'root baseline changed')
  need(JSON.stringify(Object.keys(snapshot.weights).sort())===JSON.stringify(keys),'weight vector mismatch')
  let weighted=zero
  for(const key of keys){
   const frozenWeight=prices[key],observedWeight=snapshot.weights[key]
   if(frozenWeight===undefined||observedWeight===undefined)throw new PrefixViolation('missing weight: '+key)
   const price=q(frozenWeight);need(price.n>0n&&cmp(price,q(observedWeight))===0n,'frozen positive weight changed')
   const count=integer(snapshot.counters[key]),initial=integer(base!.counters[key]),previous=integer(this.previous.counters[key])
   need(integer(snapshot.rootBaseline!.counters[key])===initial,'root counter baseline changed')
   need(count>=previous&&count>=initial,'counter rollback: '+key);weighted=add(weighted,{n:(count-initial)*price.n,d:price.d})
  }
  need(cmp(weighted,sub(actual,q(base!.actual)))===0n,'exact raw vector disagrees with actual')
  need(Array.isArray(snapshot.activeEndpoints)&&snapshot.activeEndpoints.length>0,'missing active endpoint stack')
  const ids=new Set<number>();let minimum:Q|undefined,roots=0
  for(const endpoint of snapshot.activeEndpoints){need(Number.isSafeInteger(endpoint.id)&&endpoint.id>=0&&!ids.has(endpoint.id),'endpoint identity');ids.add(endpoint.id);need(['root','scope','work-cap','deadline'].includes(endpoint.kind),'endpoint kind');if(endpoint.kind==='root')roots++;const end=q(endpoint.end);if(!minimum||cmp(end,minimum)<0n)minimum=end}
  need(roots===1,'exactly one active finite root required');need(snapshot.effectiveEnd!==null,'finite effective endpoint required')
  need(cmp(q(snapshot.effectiveEnd!),minimum!)===0n,'effective endpoint is not min(active endpoints)')
  need(cmp(add(actual,reserved),minimum!)<=0n,'actual + reserved exceeds min(active endpoints)')
 }
 observe(event:Event):void {
  need(Number.isSafeInteger(event.sequence)&&event.sequence>=0,'invalid event sequence')
  if(this.sequence!==undefined)need(event.sequence===this.sequence+1,'missing or repeated event')
  need(['trace-start','trace-end','reserve','start','release','invalidate','refuse','scope-enter','scope-exit'].includes(event.kind),'unknown event')
  this.check(event);this.sequence=event.sequence;this.previous=structuredClone(event);this.events++;this.kinds.add(event.kind);if(event.site)this.sites.add(event.site)
 }
 finish(snapshot:Snapshot):void {this.check(snapshot);need(q(snapshot.reserved).n===0n,'reservation leaked after unwind');this.previous=structuredClone(snapshot)}
}
