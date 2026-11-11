import {strict as a} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync,readdirSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const [current,before,source,kernelHash,checkerHash]=process.argv.slice(2)
const native=['tinyNodes','tinyTerms','reachStates','reachEdges','reachEvals','reachCompiledEvals']
const keys=['fm','fcells','plainRows','values','copies','edges','scan','pivotRows','unitRows','unfoldRows','goalNodes','translateRows','tableCells','checkSteps','astNodes','evals','cubeTests','ticks','cdclNodes','epr',...native]
const prices=[2.33,.0123,7.93,.672,.735,.0435,.0765,.599,15.6,.735,.492,7.93]
function read(dir:string,file:string){const lines=readFileSync(join(dir,file),'utf8').split('\n').filter(l=>l.startsWith('CANDIDATE_RECEIPT '));a.equal(lines.length,1,file);const env=JSON.parse(lines[0]!.slice(18)),bytes=Buffer.from(env.gzipBase64,'base64');a.equal(createHash('sha256').update(bytes).digest('hex'),env.sha256);const r=JSON.parse(gunzipSync(bytes).toString());a.equal(r.source,env.source);a.equal(r.id,env.id);return r}
function stable(v:any):any{return Array.isArray(v)?v.map(stable):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).filter(([k])=>!['wallMs','exclusiveWallMs'].includes(k)).map(([k,x])=>[k,stable(x)])):v}
const normalize=(r:any)=>stable(Object.fromEntries(Object.entries(r).filter(([k])=>!['source','target','custody'].includes(k))))
const files=readdirSync(current!).filter(f=>f.startsWith('off-candidate-')&&f.endsWith('.log')).sort();a.equal(files.length,28)
let checked=0
for(const file of files){const r=read(current!,file),old=read(before!,file);a.equal(r.source,source);a.equal(r.allowance,15000000);a.equal(r.clockReads,old.clockReads);a.equal(r.clockReads,undefined);a.equal(r.knobs.GDP_WORK_FULL,'0');a.equal(r.knobs.GDP_WORK_STEPS,'0');a.equal(r.knobs.GDP_REQUEST_QUOTIENT,undefined);a.equal(r.weights,undefined)
 a.deepEqual(r.custody,{'kernel/kernel.ts':kernelHash,'core/check.ts':checkerHash});a.deepEqual(Object.keys(r.raw),keys)
 const roots=r.phases.filter((p:any)=>p.parentId===null);a.equal(roots.length,1)
 for(const k of keys){a(Number.isSafeInteger(r.raw[k])&&r.raw[k]>=0);a.equal(roots[0].raw[k],r.raw[k]);a.equal(r.phases.reduce((n:number,p:any)=>n+p.exclusiveRaw[k],0),r.raw[k])}
 for(const k of native){a.equal(r.raw[k],0);a.equal(r.searchRaw[k],0)}
 const units=prices.reduce((n,price,i)=>n+price*r.raw[keys[i]!],0);a(Math.abs(units-r.units)<Math.max(1e-5,Math.abs(units)*1e-11))
 a(!r.result.error);if(r.result.proven){a(r.result.checked);checked++}
 a.deepEqual(normalize(r),normalize(old),file)
}
console.log('QUOTIENT_LEGACY_AUDIT '+JSON.stringify({source,receipts:28,checked,unknown:28-checked,exactNormalizedReceipts:28,zeroNativeCounters:true,clockTripwire:'not enabled in the unchanged legacy driver'}))
