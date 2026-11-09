// The 13-record projection and checkpoint source check completed on resume.
// Exact-family checker receipts are joined separately by link-lane-b-focus-audits.ts.
// Receipt-only projection. This does not search for or validate a proof tree.
import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
const root=process.env.LANE_B_PROJECTION_ROOT??'runs/track-m',family=JSON.parse(readFileSync(`${root}/range-input-v1/family.json`,'utf8'))
const read=(p:string)=>JSON.parse(readFileSync(p,'utf8')),hash=(b:Buffer)=>createHash('sha256').update(b).digest('hex')
const range:any[]=[],early:any[]=[],followup:any[]=[],original:any[]=[]
for(const [batch,names] of [['lane-b-range-pair-v1',['star-ab','star-ba']],['lane-b-early-focus-v1',['rows-only','rows-third','rows-classes','p1-base']],['lane-b-range-followup-v1',['p1-ab','p1-ba','rows-third-wall']]] as const){
 const dir=`${root}/${batch}`,placement=read(`${dir}/placement.json`)
 for(const name of names){
  const base=`${dir}/receipts/${name}`,manifest=read(`${base}/archive-manifest.json`),archive=readFileSync(`${base}/receipts.tar.gz`)
  assert.equal(hash(archive),manifest.sha256);assert.equal(archive.length,manifest.bytes)
  const cpu=placement[name];assert(cpu.exclusive);assert.equal(cpu.co_tenants,0);assert.equal(cpu.vcpus,8)
  const paired=batch==='lane-b-range-pair-v1'||name==='p1-ab'||name==='p1-ba'
  for(const side of paired?['before','after']:['run']){
   const tag=name.startsWith('p1-')?'p1':name.startsWith('star-')?'star':'rows',raw=`${base}/raw`,p=JSON.parse(gunzipSync(readFileSync(`${raw}/${side}/${tag}/capture.json.gz`)).toString()),r=p.record
   assert.deepEqual(p.m,family.m);assert.deepEqual(p.laws,family.laws);assert.deepEqual(r.passOrder,[1,0]);assert.equal(r.familySize,34);assert.equal(r.budget,6000);assert.equal(r.wallAllowance,7000)
   const qs=p.captures.filter((e:any)=>e.phase==='query'),events=r.events.filter((e:any)=>e.phase==='early-focus')
   const stages=events.reduce((o:Record<string,number>,e:any)=>(o[e.stage]=(o[e.stage]??0)+1,o),{})
   const cases=Array.from(new Set(events.flatMap((e:any)=>typeof e.value==='number'?[e.value]:[]))).sort((a:any,b:any)=>a-b).map(value=>({value,derivations:events.filter((e:any)=>e.value===value&&e.stage==='case-derivations').map((e:any)=>({proposed:e.proposed,units:e.ms})),fallback:events.filter((e:any)=>e.value===value&&['query','grow'].includes(e.stage)).map((e:any)=>({stage:e.stage,outcome:e.outcome}))}))
   const row={batch,name,side,tag,checked:r.checked,units:r.units,wallMs:r.wallMs,withinDiagnosticLine:r.withinDiagnosticLine,results:r.results,cpu,sha256:manifest.sha256,profile:r.profile,stages,cases,queryHypotheses:qs.map((e:any)=>e.hyps.length),rangeCoverage:qs.map((e:any)=>{const c=e.certificateRequest;return {reads:c.reads.length,ranges:c.insts.filter((i:any)=>i.unit===-1&&i.terms.length===1&&i.terms[0][0]===1).length}})}
   if(paired){if(side==='after')assert(row.rangeCoverage.every((q:any)=>q.reads===q.ranges));range.push(row)}else if(batch==='lane-b-early-focus-v1')early.push(row);else followup.push(row)
  }
 }
}
for(const name of ['rows-ab','rows-ba']){
 const p=JSON.parse(gunzipSync(readFileSync(`${root}/lane-b-pass-order-v1/receipts/${name}/raw/after/rows/capture.json.gz`)).toString()),r=p.record
 assert.deepEqual(p.m,family.m);assert.deepEqual(p.laws,family.laws)
 original.push({name,checked:r.checked,units:r.units,wallMs:r.wallMs,profile:r.profile,queryHypotheses:r.events.filter((e:any)=>e.phase==='query').map((e:any)=>e.hyps),last:r.events.at(-1)})
}
const out={conditional:true,projectionChecksProofs:false,familySize:34,original,range,early,followup}
writeFileSync(`${root}/lane-b-early-focus-v1/summary.json`,JSON.stringify(out,null,2)+'\n')
console.log(JSON.stringify({verifiedArchives:9,exactFamilyRecords:13,range:range.map(({name,side,units,wallMs,checked})=>({name,side,units,wallMs,checked})),early:[...early,...followup].map(({name,units,wallMs,checked,stages,cases})=>({name,units,wallMs,checked,deriveClassEvents:stages['derive-class-attempt']??0,cases}))},null,2))
