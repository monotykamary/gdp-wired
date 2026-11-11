import {strict as a} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync,readdirSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const [dir,source,baseline]=process.argv.slice(2)
const stable=(v:any):any=>Array.isArray(v)?v.map(stable):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).filter(([k])=>!['wallMs','exclusiveWallMs'].includes(k)).map(([k,x])=>[k,stable(x)])):v
const normalize=(r:any)=>stable(Object.fromEntries(Object.entries(r).filter(([k])=>!['source','target','custody'].includes(k))))
const files=readdirSync(dir!).filter(f=>f.startsWith('default-pair-')&&f.endsWith('.log')).sort();a.equal(files.length,28)
const rows=files.map(file=>{
 const records=readFileSync(join(dir!,file),'utf8').split('\n').filter(l=>l.startsWith('CANDIDATE_RECEIPT ')).map(line=>{
  const envelope=JSON.parse(line.slice('CANDIDATE_RECEIPT '.length)),bytes=Buffer.from(envelope.gzipBase64,'base64');a.equal(createHash('sha256').update(bytes).digest('hex'),envelope.sha256)
  const r=JSON.parse(gunzipSync(bytes).toString());a.equal(r.source,envelope.source);a.equal(r.id,envelope.id);a.equal(r.target,envelope.target);a.equal(r.allowance,15000000)
  a.deepEqual(r.knobs,{GDP_WORK_FULL:'0',GDP_WORK_STEPS:'0'});a.equal(r.weights,undefined);a.equal(r.clockReads,undefined);a(!r.result.error)
  const root=r.phases.filter((p:any)=>p.parentId===null);a.equal(root.length,1)
  for(const [key,value]of Object.entries(r.raw)){a(Number.isSafeInteger(value)&&Number(value)>=0);a.equal(root[0].raw[key],value);a.equal(r.phases.reduce((n:number,p:any)=>n+p.exclusiveRaw[key],0),value)}
  for(const key of ['tinyNodes','tinyTerms','reachStates','reachEdges','reachEvals','reachCompiledEvals'])a.equal(r.raw[key],0)
  if(r.result.proven)a(r.result.checked)
  return r
 });a.equal(records.length,2,file)
 const before=records.find(r=>r.target==='baseline'),after=records.find(r=>r.target==='candidate');a(before&&after);a.equal(before.source,baseline);a.equal(after.source,source)
 a.equal(after.id,file.slice('default-pair-'.length,-4));a.deepEqual(after.custody,before.custody);a.deepEqual(normalize(after),normalize(before),file)
 return{id:after.id,verdict:after.result.verdict,units:after.units,generated:after.generated?.count}
})
console.log('INTEGRATED_DEFAULTS '+JSON.stringify({source,baseline,models:28,exactNormalizedPairs:28,checked:rows.filter(r=>r.verdict==='proven').length,unknown:rows.filter(r=>r.verdict==='unknown').length,rows,scope:'literal feature-off legacy counted-clock compatibility; not timing or a W cap claim'}))
