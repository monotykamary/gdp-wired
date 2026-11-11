import {strict as a} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync,readdirSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const [current,before,source,kernelHash,checkerHash]=process.argv.slice(2)
const keys=['fm','fcells','plainRows','values','copies','edges','scan','pivotRows','unitRows','unfoldRows','goalNodes','translateRows','tableCells','checkSteps','astNodes','evals','cubeTests','ticks','cdclNodes','epr','tinyNodes','tinyTerms','reachStates','reachEdges','reachEvals','reachCompiledEvals']
const prices=[2.33,.0123,7.93,.672,.735,.0435,.0765,.599,15.6,.735,.492,7.93]
function read(dir:string,file:string){
 const lines=readFileSync(join(dir,file),'utf8').split('\n').filter(s=>s.startsWith('CANDIDATE_RECEIPT '));a.equal(lines.length,1,file)
 const envelope=JSON.parse(lines[0]!.slice(18)),bytes=Buffer.from(envelope.gzipBase64,'base64')
 a.equal(createHash('sha256').update(bytes).digest('hex'),envelope.sha256,file)
 const r=JSON.parse(gunzipSync(bytes).toString());a.equal(r.source,envelope.source);a.equal(r.id,envelope.id);a.equal(r.target,envelope.target);a.equal(r.allowance,envelope.allowance)
 return r
}
function stable(v:any):any{return Array.isArray(v)?v.map(stable):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).filter(([k])=>!['wallMs','exclusiveWallMs'].includes(k)).map(([k,x])=>[k,stable(x)])):v}
function normalize(r:any){const copy={...r,knobs:{...r.knobs}};delete copy.source;delete copy.target;delete copy.custody;delete copy.knobs.GDP_REQUEST_QUOTIENT;return stable(copy)}
function check(r:any,id:string,mode:string){
 a.equal(r.source,source);a.equal(r.id,id);a.equal(r.target,mode);a.equal(r.allowance,15000000)
 a.deepEqual(r.custody,{'kernel/kernel.ts':kernelHash,'core/check.ts':checkerHash})
 a.equal(r.knobs.GDP_WORK_FULL,'1');a.equal(r.knobs.GDP_WORK_STEPS,'0');a.equal(r.knobs.GDP_REQUEST_QUOTIENT,mode==='off'?'0':'1');a.equal(r.clockReads,0)
 a.deepEqual(Object.keys(r.raw),keys);a.deepEqual(Object.keys(r.searchRaw),keys);a.deepEqual(Object.keys(r.weights),keys.slice(12))
 for(const weight of Object.values(r.weights) as number[])a(Number.isFinite(weight)&&weight>0)
 const roots=r.phases.filter((p:any)=>p.parentId===null);a.equal(roots.length,1)
 const ids=new Set(r.phases.map((p:any)=>p.id));a.equal(ids.size,r.phases.length)
 for(const phase of r.phases)if(phase.parentId!==null)a(ids.has(phase.parentId),'missing phase parent')
 for(const k of keys){
  a(Number.isSafeInteger(r.raw[k])&&r.raw[k]>=0,k);a(Number.isSafeInteger(r.searchRaw[k])&&r.searchRaw[k]>=0,k)
  a.equal(roots[0].raw[k],r.raw[k]);a.equal(r.phases.reduce((n:number,p:any)=>n+p.exclusiveRaw[k],0),r.raw[k])
 }
 const weigh=(raw:any)=>keys.reduce((n,k,i)=>n+raw[k]*(i<12?prices[i]!:(r.weights[k]??0)),0)
 for(const [raw,actual]of[[r.raw,r.units],[r.searchRaw,r.searchUnits]])a(Math.abs(weigh(raw)-actual)<Math.max(1e-5,Math.abs(actual)*1e-11),'unit recomputation')
 a(!r.result.error,JSON.stringify(r.result));a.notEqual(r.result.verdict,'refuted');if(r.result.proven)a(r.result.checked)
 a(r.searchUnits<=15001024,JSON.stringify({id,mode,searchUnits:r.searchUnits}))
}
const files=readdirSync(current!).filter(f=>f.startsWith('quotient-off-')&&f.endsWith('.log')).sort();a.equal(files.length,28)
const rows:any[]=[],baselineDrift:string[]=[],repeatDrift:string[]=[],candidateDrift:string[]=[],verdictDrift:string[]=[],lostProofs:string[]=[]
for(const file of files){
 const id=file.slice('quotient-off-'.length,-4),off=read(current!,file),on=read(current!,'quotient-on-'+id+'.log'),repeat=read(current!,'quotient-repeat-'+id+'.log'),old=read(before!,'strict-'+id+'.log')
 check(off,id,'off');check(on,id,'on');check(repeat,id,'repeat')
 if(JSON.stringify(normalize(off))!==JSON.stringify(normalize(old)))baselineDrift.push(id)
 if(JSON.stringify(normalize(on))!==JSON.stringify(normalize(repeat)))repeatDrift.push(id)
 if(off.generated&&(!on.generated||off.generated.hash!==on.generated.hash))candidateDrift.push(id)
 if(off.generated&&off.result.verdict!==on.result.verdict)verdictDrift.push(id)
 if(off.result.proven&&!(on.result.proven&&on.result.checked))lostProofs.push(id)
 rows.push({id,before:off.result.verdict,after:on.result.verdict,beforeUnits:off.searchUnits,afterUnits:on.searchUnits,beforeCandidates:off.generated?.count,afterCandidates:on.generated?.count,candidatesEqual:off.generated?off.generated.hash===on.generated?.hash:null,repeatEqual:!repeatDrift.includes(id),beforeWhy:off.result.why,afterWhy:on.result.why})
}
console.log('QUOTIENT_CENSUS_AUDIT '+JSON.stringify({source,receipts:84,clockReads:0,maxUnits:Math.max(...rows.map(r=>Math.max(r.beforeUnits,r.afterUnits))),beforeProven:rows.filter(r=>r.before==='proven').length,afterProven:rows.filter(r=>r.after==='proven').length,baselineDrift,repeatDrift,candidateDrift,verdictDrift,lostProofs,rows}))
a.deepEqual(baselineDrift,[],'quotient-off no longer matches the gated release baseline')
a.deepEqual(repeatDrift,[],'same-input/same-W run is not deterministic')
a.deepEqual(candidateDrift,[],'completed baseline generation changed its candidate family')
a.deepEqual(verdictDrift,[],'verdict changed after already-completed baseline generation')
a.deepEqual(lostProofs,[],'lost checked proof')
