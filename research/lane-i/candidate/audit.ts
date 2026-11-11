import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {readdirSync,readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {gunzipSync} from 'node:zlib'
const keys=['fm','fcells','plainRows','values','copies','edges','scan','pivotRows','unitRows','unfoldRows','goalNodes','translateRows','tableCells','checkSteps','astNodes','evals','cubeTests','ticks','cdclNodes','epr']
const weights=[2.33,0.0123,7.93,0.672,0.735,0.0435,0.0765,0.599,15.6,0.735,0.492,7.93,1,1,1,1,1,1,1,1]
export function validate(data:any){
 assert.equal(data.schema,'lane-i-candidate-v1');assert.equal(data.variant,'original');assert.equal(data.unitStatus,'UNCALIBRATED');assert.equal(data.status,'PENDING-D')
 assert.deepEqual(Object.keys(data.weights).sort(),keys.slice(12).sort());for(const value of Object.values(data.weights))assert.equal(value,1)
 for(const key of keys)assert(Number.isSafeInteger(data.raw[key])&&data.raw[key]>=0,`bad raw ${key}`)
 const root=data.phases.filter((p:any)=>p.parentId===null);assert.equal(root.length,1)
 for(const key of keys){assert.equal(root[0].raw[key],data.raw[key]);assert.equal(data.phases.reduce((sum:number,p:any)=>sum+p.exclusiveRaw[key],0),data.raw[key],`exclusive ${key}`)}
 const expected=keys.reduce((sum,key,i)=>sum+data.raw[key]*weights[i]!,0)
 assert(Math.abs(expected-data.units)<=Math.max(1e-5,Math.abs(expected)*1e-12),'weighted total mismatch')
 if(data.result.verdict==='proven')assert(data.result.proven&&data.result.checked,'unchecked proven result')
 return true
}
if(import.meta.main){
 const [out,...directories]=process.argv.slice(2);if(!out||!directories.length)throw Error('audit OUTPUT-DIR RUN-DIR...')
 mkdirSync(out,{recursive:true});mkdirSync(join(out,'receipts'),{recursive:true})
 const records=new Map<string,any>(),summaries=new Map<string,any>()
 const key=(row:any)=>`${row.target}:${row.id}:${row.allowance}`
 for(const directory of directories)for(const file of readdirSync(directory).filter(file=>file.endsWith('.log'))){
  for(const line of readFileSync(join(directory,file),'utf8').split('\n')){
   if(line.startsWith('CANDIDATE_CASE ')){const row=JSON.parse(line.slice(15));assert(!summaries.has(key(row)),'duplicate case '+key(row));summaries.set(key(row),row)}
   if(!line.startsWith('CANDIDATE_RECEIPT '))continue
   const envelope=JSON.parse(line.slice(18)),bytes=Buffer.from(envelope.gzipBase64,'base64'),actual=createHash('sha256').update(bytes).digest('hex')
   assert.equal(actual,envelope.sha256);const row=JSON.parse(gunzipSync(bytes).toString());validate(row);assert.equal(key(row),key(envelope));assert.equal(row.source,envelope.source);assert(!records.has(key(row)),'duplicate receipt '+key(row))
   records.set(key(row),row);writeFileSync(join(out,'receipts',`${row.target}-${row.id}-${row.allowance}.json.gz`),bytes)
  }
 }
 for(const [id,row]of records){const summary=summaries.get(id);assert(summary,'missing summary');assert.equal(summary.result.verdict,row.result.verdict);assert.equal(summary.searchUnits,row.searchUnits)}
 const ids=JSON.parse(readFileSync(new URL('./roster.json',import.meta.url),'utf8')) as string[]
 const census=ids.filter(id=>id!=='mldr').map(id=>{const baseline=records.get(`baseline:${id}:15000000`),candidate=records.get(`candidate:${id}:15000000`);return {id,baseline:baseline?.result.verdict??'missing',candidate:candidate?.result.verdict??'missing',noLoss:!!baseline&&!!candidate&&!['error','refuted'].includes(baseline.result.verdict)&&!['error','refuted'].includes(candidate.result.verdict)&&(baseline.result.verdict!=='proven'||candidate.result.verdict==='proven'),baselineUnits:baseline?.searchUnits,candidateUnits:candidate?.searchUnits}})
 const mldr=[...records.values()].filter(r=>r.id==='mldr').map(row=>({source:row.source,target:row.target,allowance:row.allowance,result:row.result,searchUnits:row.searchUnits,generated:row.generated,phases:Object.values(row.phases.reduce((acc:any,p:any)=>{const a=acc[p.name]??={name:p.name,calls:0,units:0,incomplete:0};a.calls++;a.units+=p.exclusiveUnits;a.incomplete+=Number(!p.completed);return acc},{})).sort((a:any,b:any)=>b.units-a.units),events:row.events,queries:row.queries}))
 const result={status:'PENDING-D',unitStatus:'UNCALIBRATED',receipts:records.size,census,complete:census.every(row=>!['missing','error'].includes(row.baseline)&&!['missing','error'].includes(row.candidate)),noLoss:census.every(row=>row.noLoss),mldr}
 writeFileSync(join(out,'audit.json'),JSON.stringify(result,null,2)+'\n')
 console.log('CANDIDATE_AUDIT '+JSON.stringify({receipts:records.size,complete:result.complete,noLoss:result.noLoss,census, mldr:mldr.map(row=>({target:row.target,allowance:row.allowance,result:row.result,searchUnits:row.searchUnits,generated:row.generated,phases:row.phases}))}))
}
