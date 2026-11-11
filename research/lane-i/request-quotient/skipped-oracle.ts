import {strict as a} from 'node:assert'
import {createHash} from 'node:crypto'
export type RefusalSite = {file:string,sha256:string,line:number,expression:string}
type Origin = RefusalSite & {guardSHA256:string}
type Bucket = {kind:'guard-refusal'|'unexpected',exceptionClass:string,message:string,origin?:Origin,count:number}
export class UnexpectedSkippedOutcome extends Error {
 constructor(readonly detail:Bucket,cause:unknown){super('unexpected skipped-request exception: '+JSON.stringify(detail),{cause});this.name='UnexpectedSkippedOutcome'}
}
export class SkippedRequestOracle {
 readonly totals={skipped:0,matched:0,refused:0,kept:0,unexpected:0}
 private readonly representatives=new WeakMap<object,Map<number,string>>()
 private readonly guards=new WeakMap<object,Origin>()
 private readonly guardHashes=new WeakMap<object,string>()
 private readonly buckets=new Map<string,Bucket>()
 constructor(readonly site:RefusalSite,private readonly canonical:(m:any,s:any)=>string){}
 // Called ONLY by the adapter at the one source-hash-bound assumption-failure
 // throw. Neither the exception class nor its message is sufficient evidence.
 assumptionFailure(error:RangeError,m:{name:string,assume?:unknown}):RangeError{
  a.equal(Object.getPrototypeOf(error),RangeError.prototype)
  a.notEqual(m.assume,undefined)
  a.equal(error.message,`${m.name}: the request fails the rule's assumption, so no proof covers the step it would take`)
  let guardSHA256=this.guardHashes.get(m)
  if(!guardSHA256){guardSHA256=createHash('sha256').update(JSON.stringify(m.assume)).digest('hex');this.guardHashes.set(m,guardSHA256)}
  this.guards.set(error,{...this.site,guardSHA256})
  return error
 }
 private record(error:unknown):void{
  const origin=error&&typeof error==='object'?this.guards.get(error):undefined
  const exceptionClass=error instanceof Error?error.constructor.name:typeof error
  const message=error instanceof Error?error.message:String(error)
  const bucket:Bucket={kind:origin?'guard-refusal':'unexpected',exceptionClass,message,...(origin?{origin}:{}),count:0}
  const key=JSON.stringify(bucket),old=this.buckets.get(key)
  if(old)old.count++;else{bucket.count=1;this.buckets.set(key,bucket)}
  if(origin){this.totals.refused++;return}
  this.totals.unexpected++
  throw new UnexpectedSkippedOutcome({...bucket,count:1},error)
 }
 keep(m:any,st:object,cls:number,next:any):void{
  let map=this.representatives.get(st);if(!map){map=new Map();this.representatives.set(st,map)}
  a(!map.has(cls));map.set(cls,this.canonical(m,next));this.totals.kept++
 }
 skip(m:any,p:any,st:object,r:any,cls:number,step:(p:any,st:any,r:any)=>any):void{
  this.totals.skipped++
  const expected=this.representatives.get(st)?.get(cls);a.notEqual(expected,undefined,'missing successful class representative')
  let next:any
  try{next=step(p,st,r)}catch(error){this.record(error);return}
  // Deliberately outside the catch: a wrong successor is never a refusal.
  a.equal(this.canonical(m,next),expected,'distinct skipped successor')
  this.totals.matched++
 }
 snapshot(){return{...this.totals,exceptions:[...this.buckets.values()].map(b=>({...b})).sort((a,b)=>JSON.stringify(a).localeCompare(JSON.stringify(b))),refusalKinds:{guard:this.totals.refused,precondition:0,declaredFailure:0,unexpected:this.totals.unexpected}}}
}
export function exceptionDifference(before:ReturnType<SkippedRequestOracle['snapshot']>,after:ReturnType<SkippedRequestOracle['snapshot']>){
 const key=(b:Bucket)=>JSON.stringify({...b,count:0}),prior=new Map(before.exceptions.map(b=>[key(b),b.count]))
 return after.exceptions.map(b=>({...b,count:b.count-(prior.get(key(b))??0)})).filter(b=>b.count>0)
}
