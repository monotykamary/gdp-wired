import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {readdirSync,readFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const [onDir,beforeDir,offDir,oldOffDir,source]=process.argv.slice(2)
if(!onDir||!beforeDir||!offDir||!oldOffDir||!source)throw Error('audit ON BEFORE OFF OLD_OFF SOURCE')
function load(dir:string,prefix:string){
 const out=new Map<string,any>()
 for(const file of readdirSync(dir).filter(f=>f.endsWith('.log')&&f.startsWith(prefix))){
  const text=readFileSync(join(dir,file),'utf8'),line=text.split('\n').find(s=>s.startsWith('CANDIDATE_RECEIPT '))
  assert(line,'missing receipt '+file)
  const env=JSON.parse(line.slice(18)),bytes=Buffer.from(env.gzipBase64,'base64')
  assert.equal(createHash('sha256').update(bytes).digest('hex'),env.sha256)
  const r=JSON.parse(gunzipSync(bytes).toString())
  assert(!out.has(r.id));assert.equal(r.allowance,15000000);out.set(r.id,r)
  const root=r.phases.filter((p:any)=>p.parentId===null);assert.equal(root.length,1)
  for(const key of Object.keys(r.raw)){
   assert.equal(root[0].raw[key],r.raw[key]);assert.equal(r.phases.reduce((s:number,p:any)=>s+p.exclusiveRaw[key],0),r.raw[key])
  }
 }
 assert.equal(out.size,28);return out
}
const now=load(onDir,'strict-'),before=load(beforeDir,'strict-'),off=load(offDir,'off-candidate-'),oldOff=load(oldOffDir,'off-baseline-')
const rows=[]
for(const [id,n] of now){
 const b=before.get(id),x=off.get(id),y=oldOff.get(id)
 assert(b&&x&&y);assert.equal(n.source,source);assert.equal(x.source,source)
 assert.equal(n.knobs.GDP_WORK_FULL,'1');assert.equal(n.clockReads,0)
 assert.equal(n.result.proven,b.result.proven,id);assert.equal(n.result.checked,b.result.checked,id);assert.equal(n.result.verdict,b.result.verdict,id)
 assert(n.searchUnits<=15000000+1024+1e-6,`over cap: ${id} ${n.searchUnits}`)
 if(n.result.proven){assert.deepEqual(n.raw,b.raw,id);assert.deepEqual(n.queries,b.queries,id)}
 else assert.equal(n.result.verdict,'unknown',id)
 assert.equal(x.knobs.GDP_WORK_FULL,'0');assert.equal(y.knobs.GDP_WORK_FULL,'0')
 assert.equal(x.knobs.GDP_WORK_STEPS,'0');assert.equal(y.knobs.GDP_WORK_STEPS,'0')
 const omitProvenance=(r:any)=>Object.fromEntries(Object.entries(r).filter(([k])=>k!=='source'&&k!=='target'))
 assert.deepEqual(omitProvenance(x),omitProvenance(y),'flags-off drift '+id)
 rows.push({id,before:b.searchUnits,after:n.searchUnits,slack:Math.max(0,n.searchUnits-15000000),verdict:n.result.verdict,checked:n.result.checked,why:n.result.why,flagsOffIdentical:true})
}
console.log('HARD_CAP_AUDIT '+JSON.stringify({source,allowance:15000000,allowedSlack:1024,maxUsed:Math.max(...rows.map(r=>r.after)),maxSlack:Math.max(...rows.map(r=>r.slack)),proved:rows.filter(r=>r.verdict==='proven').length,unknown:rows.filter(r=>r.verdict==='unknown').length,zeroForbiddenClockReads:true,flagsOffIdentical:28,rows}))
