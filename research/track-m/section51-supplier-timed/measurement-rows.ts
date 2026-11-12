// Offline attribution of the unchanged native counts stream. No prover imports.
import {WORK_KEYS,recomputeDeltas} from './pair-checks.ts'
type Q={numerator:string,denominator:string}
const need=(v:unknown,s:string):void=>{if(!v)throw Error(s)}
const integer=(v:unknown):bigint=>{need(typeof v==='string'&&/^(0|[1-9]\d*)$/.test(v as string),'invalid measurement integer');return BigInt(v as string)}
const gcd=(a:bigint,b:bigint):bigint=>b===0n?a:gcd(b,a%b)
const q=(n:bigint,d=1n):Q=>{need(n>=0n&&d>0n,'negative work or invalid denominator');const g=gcd(n,d);return {numerator:String(n/g),denominator:String(d/g)}}
const add=(a:Q,b:Q):Q=>q(integer(a.numerator)*integer(b.denominator)+integer(b.numerator)*integer(a.denominator),integer(a.denominator)*integer(b.denominator))
export const subtractWork=(a:Q,b:Q):Q=>q(integer(a.numerator)*integer(b.denominator)-integer(b.numerator)*integer(a.denominator),integer(a.denominator)*integer(b.denominator))
export function referenceSeconds(units:Q,rate:Q):Q{
 need(integer(rate.numerator)>0n&&integer(rate.denominator)>0n,'nonpositive conversion rate')
 return q(integer(units.numerator)*integer(rate.denominator),integer(units.denominator)*integer(rate.numerator))
}
const zeros=():Record<string,string>=>Object.fromEntries(WORK_KEYS.map(k=>[k,'0']))
function countersBetween(a:any,b:any):Record<string,string>{
 return Object.fromEntries(WORK_KEYS.map(k=>{const n=integer(b.counters[k])-integer(a.counters[k]);need(n>=0n,'counter regression in attributed interval');return [k,String(n)]}))
}
function weighted(c:Record<string,string>,weights:any):Q{
 return WORK_KEYS.reduce((sum,k)=>add(sum,q(integer(c[k])*integer(weights[k].numerator),integer(weights[k].denominator))),q(0n))
}
export class MeasurementRows {
 private rows=new Map<string,any>()
 private active:{law:string,snapshot:any,index:number}|undefined
 private countIndex=0
 private last:any=null
 private lastWorkEvent:any=null
 private issues:string[]=[]
 constructor(private baseline:any,private callerNames:readonly string[]){for(const n of callerNames)this.row(n)}
 private row(name:string):any{
  need(typeof name==='string'&&name.length>0,'invalid law name')
  if(!this.rows.has(name))this.rows.set(name,{name,kind:this.callerNames.includes(name)?'safety':'helper',countedUnits:q(0n),counterDeltas:zeros(),attempts:[],nativeCheckedInFamilies:[],firstCheckedAtRootUnits:null})
  return this.rows.get(name)
 }
 private cumulative(s:any):Q{return subtractWork(s.actual,this.baseline.actual)}
 private close(snapshot:any,reason:string,event:any){
  if(!this.active)return
  const {law,snapshot:start,index}=this.active,row=this.row(law),deltas=countersBetween(start,snapshot),units=subtractWork(snapshot.actual,start.actual)
  need(JSON.stringify(weighted(deltas,start.weights))===JSON.stringify(units),'interval counters and units differ')
  row.countedUnits=add(row.countedUnits,units)
  for(const k of WORK_KEYS)row.counterDeltas[k]=String(integer(row.counterDeltas[k])+integer(deltas[k]))
  row.attempts.push({fromCountRecord:index,toCountRecord:this.countIndex,reason,countedUnits:units,rootStartUnits:this.cumulative(start),rootEndUnits:this.cumulative(snapshot),counterDeltas:deltas,outcome:event?.outcome??null,held:event?.held??null,why:event?.reason??null})
  this.active=undefined
 }
 observeLedger(event:any){this.lastWorkEvent={kind:event.kind,sequence:event.sequence,site:event.site??null,sink:event.sink??null,actual:event.actual,requested:event.requested??null,granted:event.granted??null,activeEndpoints:event.activeEndpoints}}
 observe(event:any,snapshot:any){
  this.countIndex++
  this.last={phase:event?.phase??null,law:event?.law??null,goal:event?.goal??null,rootUnits:this.cumulative(snapshot)}
  if(typeof event?.law==='string')this.row(event.law)
  if(Array.isArray(event?.laws))for(const law of event.laws){const name=typeof law==='string'?law:law?.name;if(typeof name==='string')this.row(name)}
  if(event?.phase==='count-component-attempt'){
   if(this.active){this.issues.push('attempt superseded without component-result');this.close(snapshot,'superseded',null)}
   this.row(event.law);this.active={law:event.law,snapshot,index:this.countIndex}
  }else if(event?.phase==='count-component-result'){
   if(this.active?.law===event.law)this.close(snapshot,'native-component-result',event)
   else this.issues.push('component-result without matching active attempt: '+event.law)
  }
  if((event?.phase==='closed-family'||event?.phase==='closed-subfamily')&&event.checked===true){
   for(const law of event.laws??[]){const name=typeof law==='string'?law:law.name,row=this.row(name),at=this.cumulative(snapshot);row.firstCheckedAtRootUnits??=at;row.nativeCheckedInFamilies.push({phase:event.phase,atRootUnits:at})}
  }
 }
 finish(verdict:any){
  if(this.active){this.close(verdict.final,'interrupted-or-no-result',null);this.issues.push('last component has no native result')}
  const deltas=recomputeDeltas(verdict),total=this.cumulative(verdict.final),attributed=[...this.rows.values()].reduce((sum,row)=>add(sum,row.countedUnits),q(0n))
  need(JSON.stringify(weighted(deltas,verdict.initial.weights))===JSON.stringify(total),'root counters and total units differ')
  return {schema:'mldr-measurement-rows/v1',mode:'instrumented',authority:'MEASUREMENT_ONLY',qualification:false,WClaim:false,verdictAuthority:false,publicProvenAndChecked:verdict.rawVerdict?.proven===true&&verdict.rawVerdict?.checked===true,rootCeilingRaw:verdict.originalRootRaw,totalCountedUnits:total,counterDeltas:deltas,attributedCountedUnits:attributed,sharedOrUnattributedUnits:subtractWork(total,attributed),attributionComplete:this.issues.length===0,attributionIssues:this.issues,attributionMeaning:'Disjoint native count-component-attempt/result spans only. Includes dependency work inside each attempt; shared generation, screening, replay and closing remain unallocated. Not marginal per-law costs.',rows:[...this.rows.values()].map(row=>({...row,status:row.kind==='safety'&&verdict.rawVerdict?.proven===true&&verdict.rawVerdict?.checked===true?'PUBLIC_PROVEN_AND_CHECKED':row.nativeCheckedInFamilies.length?'CHECKED_NATIVE_FAMILY_MEMBER':row.attempts.length?'ATTEMPTED_NOT_CHECKED':'NOT_ATTEMPTED'})),stop:{phase:verdict.phase,lastCountEvent:this.last,lastWorkEvent:this.lastWorkEvent,error:verdict.error,rawVerdict:verdict.rawVerdict},referenceConversion:{status:'PENDING_RHO_NEW',rhoNew:null,seconds:null},checks:'Provisional/held component results are not proven+checked. Only the native checked-family events establish member checking; only the public verdict establishes complete original safety closure.'}
 }
}
