import {createHash} from 'node:crypto'
import type {ExactRaw,Snapshot,LeaseEvent,Manifest,LawIdentity,CaseAttempt,Verdict} from './contract.ts'
export const digest=(value:unknown):string=>createHash('sha256').update(JSON.stringify(value)).digest('hex')
export const identity=(law:{name:string}):LawIdentity=>({name:law.name,sha256:digest(law)})
const integer=(s:string):bigint=>{if(!/^(0|[1-9][0-9]*)$/.test(s))throw Error('invalid nonnegative integer');return BigInt(s)}
export const amount=(x:ExactRaw):readonly [bigint,bigint]=>{const n=integer(x.numerator),d=integer(x.denominator);if(!d)throw Error('zero denominator');return[n,d]}
export const cmp=(a:ExactRaw,b:ExactRaw):number=>{const[x,y]=amount(a),[u,v]=amount(b),d=x*v-u*y;return d<0n?-1:d>0n?1:0}
export const add=(a:ExactRaw,b:ExactRaw):ExactRaw=>{const[x,y]=amount(a),[u,v]=amount(b);return{numerator:String(x*v+u*y),denominator:String(y*v)}}
export const delta=(a:ExactRaw,b:ExactRaw):ExactRaw=>{const[x,y]=amount(a),[u,v]=amount(b),n=x*v-u*y;if(n<0n)throw Error('spent work decreased');return{numerator:String(n),denominator:String(y*v)}}
const zero:ExactRaw={numerator:'0',denominator:'1'}
const sameKeys=(a:readonly string[],b:readonly string[])=>JSON.stringify([...a].sort())===JSON.stringify([...b].sort())
export function assertSnapshot(s:Snapshot,keys:readonly string[],weightsSha256?:string):void{
 if(s.version!=='strict-work-v1'||![s.rootEpoch,s.scopeEpoch,s.counterEpoch].every(n=>Number.isSafeInteger(n)&&n>=0))throw Error('wrong meter identity/epoch')
 amount(s.actual);amount(s.reserved)
 if(!sameKeys(Object.keys(s.counters),keys)||!sameKeys(Object.keys(s.weights),keys))throw Error('counter domain mismatch')
 if(weightsSha256&&digest(s.weights)!==weightsSha256)throw Error('weight identity mismatch')
 const ids=new Set<number>();let minimum:ExactRaw|null=null
 for(const e of s.activeEndpoints){if(!Number.isSafeInteger(e.id)||ids.has(e.id))throw Error('duplicate endpoint');ids.add(e.id);amount(e.end);if(cmp(add(s.actual,s.reserved),e.end)>0)throw Error('F+R exceeds active E');if(!minimum||cmp(e.end,minimum)<0)minimum=e.end}
 if((minimum===null)!==(s.effectiveEnd===null)||minimum&&s.effectiveEnd&&cmp(minimum,s.effectiveEnd)!==0)throw Error('effective endpoint is not the minimum')
 for(const key of keys){integer(s.counters[key]!);amount(s.weights[key]!)}
 if(s.rootBaseline){
  if(!s.activeEndpoints.some(e=>e.kind==='root'))throw Error('active root has no root endpoint')
  if(!sameKeys(Object.keys(s.rootBaseline.counters),keys))throw Error('baseline domain mismatch')
  let weighted=s.rootBaseline.actual
  for(const key of keys){const n=integer(s.counters[key]!)-integer(s.rootBaseline.counters[key]!);if(n<0n)throw Error('counter precedes root baseline');weighted=add(weighted,{numerator:String(n*amount(s.weights[key]!)[0]),denominator:s.weights[key]!.denominator})}
  if(cmp(weighted,s.actual)!==0)throw Error('weighted counters disagree with F')
 }
}
// Audit every event online; retaining a whole atom-level trace can exhaust the proof worker.
export class TraceAudit{
 private sequence=-1
 private first:LeaseEvent['kind']|undefined
 private last:LeaseEvent['kind']|undefined
 private active=false
 private failure:string|undefined
 private count=0
 private actual=new Map<number,ExactRaw>()
 private hash=createHash('sha256')
 private head:LeaseEvent[]=[]
 private tail:LeaseEvent[]=[]
 constructor(private keys:readonly string[],private weightsSha256:string){}
 observe(e:LeaseEvent):void{
  this.count++;this.hash.update(JSON.stringify(e)+'\n');this.first??=e.kind;this.last=e.kind
  if(this.head.length<8)this.head.push(e);else{this.tail.push(e);if(this.tail.length>8)this.tail.shift()}
  if(this.failure)return
  try{if(!Number.isSafeInteger(e.sequence)||e.sequence<=this.sequence)throw Error('nonmonotone trace sequence');this.sequence=e.sequence;assertSnapshot(e,this.keys,this.weightsSha256);const before=this.actual.get(e.rootEpoch);if(before&&cmp(e.actual,before)<0)throw Error('F refunded');this.actual.set(e.rootEpoch,e.actual);if(e.rootBaseline)this.active=true}catch(error){this.failure=String(error)}
 }
 finish():void{if(this.failure)throw Error(this.failure);if(this.count<2||this.first!=='trace-start'||this.last!=='trace-end')throw Error('incomplete meter trace');if(!this.active)throw Error('no active strict-work root observed')}
 receipt(){return{events:this.count,sha256:this.hash.copy().digest('hex'),head:this.head,tail:this.tail,completeRawArchive:false,firstFailure:this.failure??null}}
}
export function assertTrace(events:readonly LeaseEvent[],keys:readonly string[],weightsSha256:string):void{const audit=new TraceAudit(keys,weightsSha256);for(const event of events)audit.observe(event);audit.finish()}
export function assertManifest(m:Manifest):void{
 if(m.version!=='c2-production-gates-v1'||!m.candidate||!m.flags||!m.halfLaw)throw Error('missing manifest')
 for(const hash of [m.candidate.commit,m.candidate.tree])if(!/^[a-f0-9]{40}$/.test(hash))throw Error('unbound candidate')
 for(const hash of [m.candidate.sourceClosureSha256,m.weightsSha256,m.originalMachineSha256])if(!/^[a-f0-9]{64}$/.test(hash))throw Error('unbound identity')
 if(m.flags.GDP_WORK_FULL!=='1'||m.flags.GDP_WORK_STEPS!=='0'||m.flags.GDP_COUNT_C2_LEMMAS!=='1')throw Error('wrong C2/full-work profile')
 if(m.workKeys.length!==26||new Set(m.workKeys).size!==26)throw Error('expected exact 26-counter domain')
 amount(m.rootGrant);integer(m.searchWorkRaw)
 if(!Number.isSafeInteger(m.wallMs)||m.wallMs<=0||!m.protocolId||Object.entries(m.flags).some(([k,v])=>!k.startsWith('GDP_')||typeof v!=='string'))throw Error('invalid run parameters')
 if([...m.candidateRoster,...m.closedRoster].some(x=>!x.name||!/^([a-f0-9]{64})$/.test(x.sha256)))throw Error('unbound law identity')
 if(![44,49].includes(m.candidateRoster.length))throw Error('old 19-law roster cannot substitute')
 const all=[...m.closedRoster,...m.exclusions.map(e=>e.law)]
 if(!sameKeys(all.map(digest),m.candidateRoster.map(digest))||new Set(all.map(x=>x.name)).size!==all.length)throw Error('roster/exclusion coverage mismatch')
 if(!m.closedRoster.some(x=>digest(x)===digest(m.halfLaw)))throw Error('half target omitted from closure')
 if(m.exclusions.some(x=>!x.reason.trim())||!m.operations.length||new Set(m.operations.map(x=>x.value)).size!==m.operations.length)throw Error('missing exclusion or operation identity')
}
export function assertRoster(actual:readonly {name:string}[],expected:readonly LawIdentity[]):void{if(JSON.stringify(actual.map(identity))!==JSON.stringify(expected))throw Error('exact roster mismatch')}
export function halfCap(attempts:readonly CaseAttempt[]):Verdict&{units?:ExactRaw,allowance?:ExactRaw}{
 const selected=attempts.filter(a=>a.identity.kind==='threshold-replace')
 if(!selected.length)return{status:'NOT_RUN',reason:'replacement route not observed'}
 if(selected.length!==1)return{status:'NOT_RUN',reason:'section46 typed retry/fuel binding has not landed; no retry inference from phase strings'}
 const a=selected[0]!;if(!a.end||!a.returned)return{status:'UNKNOWN',reason:'replacement declined, threw, or expired'}
 if(!a.start.rootBaseline||a.start.rootEpoch!==a.end.rootEpoch)return{status:'FAIL',reason:'case root identity changed'}
 const slice=a.slice;if(!slice)return{status:'NOT_RUN',reason:'explicit exact case-slice binding absent; no deadline or reason-text inference'}
 if(slice.kind!=='case'||slice.key!=='op:'+a.identity.value||slice.rootEpoch!==a.start.rootEpoch)return{status:'FAIL',reason:'wrong case slice identity'}
 const before=new Set(a.start.activeEndpoints.map(e=>e.id));const first=a.events.find(e=>e.kind==='scope-enter'&&e.activeEndpoints.some(p=>p.id===slice.scopeId&&!before.has(p.id)&&p.kind==='scope'))
 const endpoint=first?.activeEndpoints.find(p=>p.id===slice.scopeId&&!before.has(p.id)&&p.kind==='scope')
 if(first&&a.events.slice(0,a.events.indexOf(first)).some(e=>e.kind==='start'))return{status:'FAIL',reason:'work started before the case deadline lease'}
 if(!endpoint)return{status:'NOT_RUN',reason:'exact constructor scope ID absent from trace; clock telemetry is not a fallback'}
 try{const units=delta(a.end.actual,a.start.actual),allowance=delta(endpoint.end,a.start.actual);if(cmp(allowance,slice.allocation)>0)return{status:'FAIL',reason:'scope exceeds exact case allocation'};if(cmp(units,allowance)>0)return{status:'FAIL',reason:'replacement exceeded its actual case lease',units,allowance};return{status:'PASS',reason:'replacement completed within its observed case lease',units,allowance}}catch(error){return{status:'FAIL',reason:String(error)}}
}
export const zeroRaw=zero
