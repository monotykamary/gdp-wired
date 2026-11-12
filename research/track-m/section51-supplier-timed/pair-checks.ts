// Pure receipt arithmetic and acceptance policy. No native/prover imports.
import {positiveRaw} from './root-policy.ts'
export const WORK_KEYS=['fm','fcells','plainRows','values','copies','edges','scan','pivotRows','unitRows','unfoldRows','goalNodes','translateRows','tableCells','checkSteps','astNodes','evals','cubeTests','ticks','cdclNodes','epr','tinyNodes','tinyTerms','reachStates','reachEdges','reachEvals','reachCompiledEvals'].sort()
export const stable=(x:any):string=>JSON.stringify(x,(_k,v)=>v&&typeof v==='object'&&!Array.isArray(v)?Object.fromEntries(Object.keys(v).sort().map(k=>[k,v[k]])):v)
function need(v:unknown,message:string):asserts v{if(!v)throw Error(message)}
const keysOK=(v:any)=>v&&stable(Object.keys(v).sort())===stable(WORK_KEYS)
const integer=(v:any)=>{need(typeof v==='string'&&/^(0|[1-9]\d*)$/.test(v),'invalid raw counter');return BigInt(v)}
const raw=(v:any)=>{need(v&&typeof v.numerator==='string'&&typeof v.denominator==='string','invalid exact work');const n=integer(v.numerator),d=integer(v.denominator);need(d>0n,'zero denominator');return {n,d}}
const plus=(a:{n:bigint,d:bigint},b:{n:bigint,d:bigint})=>({n:a.n*b.d+b.n*a.d,d:a.d*b.d})
const le=(a:{n:bigint,d:bigint},b:{n:bigint,d:bigint})=>a.n*b.d<=b.n*a.d
export function rootOK(s:any,rootUnits:bigint):boolean{
 if(!s.rootBaseline||!Array.isArray(s.activeEndpoints)||!keysOK(s.weights)||!keysOK(s.counters)||!keysOK(s.rootBaseline.counters))return false
 const roots=s.activeEndpoints.filter((e:any)=>e.kind==='root');if(roots.length!==1)return false
 const a=raw(s.actual),r=raw(s.reserved),base=raw(s.rootBaseline.actual),end=raw(roots[0].end)
 if(end.n*base.d-base.n*end.d!==rootUnits*end.d*base.d||!le(base,a))return false
 if(!s.activeEndpoints.every((e:any)=>le(plus(a,r),raw(e.end))))return false
 let total={n:0n,d:1n}
 for(const k of WORK_KEYS){const count=integer(s.counters[k])-integer(s.rootBaseline.counters[k]),weight=raw(s.weights[k]);if(count<0n||weight.n===0n)return false;total=plus(total,{n:count*weight.n,d:weight.d})}
 const delta={n:a.n*base.d-base.n*a.d,d:a.d*base.d};return total.n*delta.d===delta.n*total.d
}
export function settledOK(s:any):boolean{return s.activeEndpoints?.length===0&&s.rootBaseline===null&&s.effectiveEnd===null&&raw(s.reserved).n===0n}
export function recomputeDeltas(v:any):Record<string,string>{
 const initial=v.initial,final=v.final,baseline=initial?.rootBaseline
 need(baseline&&keysOK(baseline.counters)&&keysOK(initial.counters)&&keysOK(final.counters),'incomplete 26-counter snapshots')
 need(stable(initial.counters)===stable(baseline.counters)&&stable(initial.actual)===stable(baseline.actual)&&raw(initial.reserved).n===0n,'initial snapshot differs from root baseline')
 need(stable(final.rootBaseline)===stable(baseline)&&Number.isSafeInteger(initial.rootEpoch)&&initial.rootEpoch>0&&final.rootEpoch===initial.rootEpoch,'root baseline/epoch changed')
 const validEpoch=(n:unknown)=>typeof n==='number'&&Number.isSafeInteger(n)&&n>=0
 need(validEpoch(initial.counterEpoch)&&validEpoch(final.counterEpoch),'invalid counter epoch')
 need(final.counterEpoch>=initial.counterEpoch,'counter epoch regressed')
 // Native positive lease.start(n) advances the generation once, not n times.
 const deltas:Record<string,string>={};let charged=false
 for(const k of WORK_KEYS){const d=integer(final.counters[k])-integer(baseline.counters[k]);need(d>=0n,'counter regressed: '+k);deltas[k]=String(d);charged ||= d>0n}
 need(!charged||final.counterEpoch>initial.counterEpoch,'positive counters without epoch advance')
 return deltas
}
export function comparePair(a:any,b:any,replay:any,rootRaw:string){
 const rootUnits=positiveRaw(rootRaw)
 const da=recomputeDeltas(a),db=recomputeDeltas(b),hex=(v:any)=>typeof v==='string'&&/^[0-9a-f]{64}$/.test(v)
 const checks={complete:a.diagnosticComplete===true&&b.diagnosticComplete===true,source:a.identity.sourceCommit===b.identity.sourceCommit&&a.identity.sourceCommit==='9eb09b8326fc2670fad6725f774ab1b252c4d343',tree:a.identity.sourceTree===b.identity.sourceTree&&a.identity.sourceTree==='20e56881dd613158a5ac53b3633bd8b3e3db8ed5',flags:a.identity.profileSHA256===b.identity.profileSHA256&&a.identity.profileSHA256==='a5f077dc8156a7bb550dc0ed279de96b20aa3a167c32fbaaaaad925fc9f8a272',model:hex(a.modelSHA256)&&hex(a.lawsSHA256)&&a.modelSHA256===b.modelSHA256&&a.lawsSHA256===b.lawsSHA256,root:a.originalRootRaw===rootRaw&&b.originalRootRaw===rootRaw&&a.identity.rootRaw===rootRaw&&b.identity.rootRaw===rootRaw,weights:stable(a.initial.weights)===stable(b.initial.weights)&&[a,b].every(v=>stable(v.initial.weights)===stable(v.final.weights)),verdict:a.rawVerdict!==null&&b.rawVerdict!==null&&stable(a.rawVerdict)===stable(b.rawVerdict)&&a.verdict===b.verdict,counters:stable(da)===stable(db),echoedDeltas:keysOK(a.counterDeltas)&&keysOK(b.counterDeltas)&&stable(a.counterDeltas)===stable(da)&&stable(b.counterDeltas)===stable(db),accounting:[a,b].every(v=>rootOK(v.initial,rootUnits)&&rootOK(v.final,rootUnits)&&settledOK(v.settled)&&raw(v.final.reserved).n===0n),mode:a.mode==='timed'&&!a.observerInstalled&&b.mode==='instrumented'&&b.observerInstalled,fullTrace:b.trace?.complete===true&&replay.complete===true,oracles:b.trace?.oracle?.passed===true&&replay.oraclePassed===true}
 const status=checks.fullTrace&&(b.trace?.oracle?.passed===false||replay.oraclePassed===false)?'ORACLE_VIOLATION':Object.values(checks).every(Boolean)?'EQUAL_OBSERVED_PAIR':'PAIR_REJECTED'
 return {status,rootRaw,checks,recomputedCounterDeltas:{timed:da,instrumented:db}}
}
