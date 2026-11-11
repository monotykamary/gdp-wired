import {strict as a} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync,readdirSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const [current,before,source,kernelHash,checkerHash]=process.argv.slice(2)
const old=['fm','fcells','plainRows','values','copies','edges','scan','pivotRows','unitRows','unfoldRows','goalNodes','translateRows','tableCells','checkSteps','astNodes','evals','cubeTests','ticks','cdclNodes','epr']
const native=['tinyNodes','tinyTerms','reachStates','reachEdges','reachEvals','reachCompiledEvals'],keys=[...old,...native]
const prices=[2.33,.0123,7.93,.672,.735,.0435,.0765,.599,15.6,.735,.492,7.93]
function read(dir:string,file:string){const line=readFileSync(join(dir,file),'utf8').split('\n').find(s=>s.startsWith('CANDIDATE_RECEIPT '));a(line,file);const envelope=JSON.parse(line.slice(18)),bytes=Buffer.from(envelope.gzipBase64,'base64');a.equal(createHash('sha256').update(bytes).digest('hex'),envelope.sha256,file);const r=JSON.parse(gunzipSync(bytes).toString());a.equal(r.source,envelope.source);return r}
function stable(v:any):any{return Array.isArray(v)?v.map(stable):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).filter(([k])=>!['wallMs','exclusiveWallMs',...native].includes(k)).map(([k,x])=>[k,stable(x)])):v}
const normalize=(r:any)=>stable(Object.fromEntries(Object.entries(r).filter(([k])=>!['source','target','custody'].includes(k))))
const semantic=(r:any)=>{const omit=(v:any)=>Object.fromEntries(Object.entries(v).filter(([k])=>!['astNodes','evals'].includes(k)));return normalize({...r,raw:omit(r.raw),searchRaw:omit(r.searchRaw),phases:r.phases.map((p:any)=>({...p,raw:omit(p.raw),exclusiveRaw:omit(p.exclusiveRaw)}))})}
const files=readdirSync(current!).filter(f=>f.startsWith('off-candidate-')&&f.endsWith('.log')).sort()
a.equal(files.length,28)
const rows:any[]=[],offDrift:any[]=[],regressions:any[]=[]
let semanticIdentity=0
for(const file of files){const id=file.slice(14,-4),off=read(current!,file),oldOff=read(before!,file),full=read(current!,'strict-'+id+'.log'),oldFull=read(before!,'strict-'+id+'.log')
 for(const r of[off,full]){a.equal(r.source,source);a.equal(r.allowance,15000000);a.deepEqual(r.custody,{'kernel/kernel.ts':kernelHash,'core/check.ts':checkerHash});a.deepEqual(Object.keys(r.raw),keys);a.equal(r.phases.filter((p:any)=>p.parentId===null).length,1)
  for(const k of keys){a(Number.isSafeInteger(r.raw[k])&&r.raw[k]>=0,k);a.equal(r.phases.find((p:any)=>p.parentId===null).raw[k],r.raw[k]);a.equal(r.phases.reduce((n:number,p:any)=>n+p.exclusiveRaw[k],0),r.raw[k])}
  if(r.knobs.GDP_WORK_FULL==='1'){a.deepEqual(Object.keys(r.weights),keys.slice(12));for(const weight of Object.values(r.weights) as number[])a(Number.isFinite(weight)&&weight>0)}else a.equal(r.weights,undefined)
  const units=keys.reduce((n,k,i)=>n+r.raw[k]*(i<12?prices[i]!:(r.weights?.[k]??0)),0);a(Math.abs(units-r.units)<Math.max(1e-5,Math.abs(units)*1e-11))
  a(!r.result.error,JSON.stringify(r.result));a.notEqual(r.result.verdict,'refuted');if(r.result.proven)a(r.result.checked)
 }
 a.equal(full.clockReads,0);a.equal(full.knobs.GDP_WORK_FULL,'1');a.equal(off.knobs.GDP_WORK_FULL,'0');a.equal(off.knobs.GDP_WORK_STEPS,'0')
 for(const k of native){a.equal(off.raw[k],0);a.equal(off.searchRaw[k],0);for(const p of off.phases){a.equal(p.raw[k],0);a.equal(p.exclusiveRaw[k],0)}}
 if(JSON.stringify(semantic(off))===JSON.stringify(semantic(oldOff)))semanticIdentity++
 if(oldOff.result.proven&&!(off.result.proven&&off.result.checked))regressions.push({id,mode:'off',before:oldOff.result,after:off.result})
 if(oldFull.result.proven&&!(full.result.proven&&full.result.checked))regressions.push({id,mode:'full',before:oldFull.result,after:full.result})
 if(JSON.stringify(normalize(off))!==JSON.stringify(normalize(oldOff))){const old=normalize(oldOff),next=normalize(off);offDrift.push({id,fields:Object.keys(next).filter(k=>JSON.stringify(next[k])!==JSON.stringify(old[k])),raw:Object.fromEntries(keys.filter(k=>off.raw[k]!==oldOff.raw[k]).map(k=>[k,{before:oldOff.raw[k],after:off.raw[k],delta:off.raw[k]-oldOff.raw[k]}])),searchRaw:Object.fromEntries(keys.filter(k=>off.searchRaw[k]!==oldOff.searchRaw[k]).map(k=>[k,{before:oldOff.searchRaw[k],after:off.searchRaw[k],delta:off.searchRaw[k]-oldOff.searchRaw[k]}]))})}
 a(full.searchUnits<=15001024,JSON.stringify({id,searchUnits:full.searchUnits}))
 rows.push({id,offBefore:oldOff.result.verdict,offAfter:off.result.verdict,fullBefore:oldFull.result.verdict,fullAfter:full.result.verdict,searchUnits:full.searchUnits,offExact:!offDrift.some(x=>x.id===id),candidatesBefore:oldOff.generated?.hash,candidatesAfter:off.generated?.hash})
}
const report={source,receipts:56,checkerCustodyReceipts:56,semanticIdentity,fullProven:rows.filter(r=>r.fullAfter==='proven').length,offProven:rows.filter(r=>r.offAfter==='proven').length,maxUnits:Math.max(...rows.map(r=>r.searchUnits)),offDrift,regressions,rows}
console.log('MERGE_CENSUS_AUDIT '+JSON.stringify(report))
a.equal(regressions.length,0,'lost checked verdicts')
if(process.argv[7]==='release-compatible'){
 a.equal(semanticIdentity,28,'release changed more than unpriced raw observations')
 for(const drift of offDrift)for(const field of ['raw','searchRaw'])for(const [key,value]of Object.entries(drift[field]) as [string,{delta:number}][]) {a(['evals','astNodes'].includes(key),key);a(value.delta<0,key)}
 console.log('MERGE_RELEASE_COMPATIBILITY '+JSON.stringify({source,semanticIdentity,strictRawIdentity:28-offDrift.length,unpricedRawDelta:offDrift.length,approval:'PENDING-D'}))
}else if(process.argv[7]!=='diagnose')a.equal(offDrift.length,0,'flags-off normalized receipts changed')
