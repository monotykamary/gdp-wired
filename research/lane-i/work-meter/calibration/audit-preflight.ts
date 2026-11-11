import {strict as assert} from 'node:assert'
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
import {validatePhaseLedger,meterKeys} from './contract.ts'
const pin='cd00524f01093838e9584edc4a20f71e2be10e2a'
const legacy=[2.33,.0123,7.93,.672,.735,.0435,.0765,.599,15.6,.735,.492,7.93]
export function auditPreflight(row:any, prior:any){
 assert.equal(row.source,pin);assert.equal(row.id,'consensus_epr')
 assert([15000000,50000000].includes(row.work));assert(['original','broken'].includes(row.variant))
 const bytes=gunzipSync(Buffer.from(row.receiptGzipBase64,'base64'),{maxOutputLength:8*1024*1024})
 assert.equal(createHash('sha256').update(bytes).digest('hex'),row.sha256,'complete receipt hash')
 const data=JSON.parse(bytes.toString());assert.equal(data.source,pin);assert.equal(data.id,row.id)
 for(const key of ['variant','repetition','work','weights','raw','result'])assert.deepEqual(data[key],row[key],key)
 assert.deepEqual(data.events,row.phaseEvents);assert(data.budgetExhausted)
 validatePhaseLedger(data.raw,data.events)
 assert.deepEqual(data.raw,prior.raw,'raw result must match preserved run');assert.deepEqual(data.result,prior.result)
 assert.deepEqual(data.weights,Object.fromEntries(meterKeys.slice(12).map(key=>[key,1])))
 const units=(raw:any)=>meterKeys.reduce((sum,key,i)=>sum+raw[key]*(legacy[i]??data.weights[key]),0)
 const phases=data.events.map((event:any)=>{
  assert.equal(event.unitModel,'explicit-complete');assert.deepEqual(event.weights,data.weights)
  assert(Math.abs(event.units-units(event.raw))<1e-6,'inclusive weighted units')
  assert(Math.abs(event.exclusiveUnits-units(event.exclusiveRaw))<1e-6,'exclusive weighted units')
  return {name:event.name,completed:event.completed,units:event.units,exclusiveUnits:event.exclusiveUnits,raw:event.exclusiveRaw}
 })
 assert.equal(data.raw.epr,0);assert.equal(data.raw.fm,0);assert.equal(data.raw.plainRows,0)
 const root=data.events.find((e:any)=>e.parentId===null),small=phases.find((e:any)=>e.name==='small')
 assert(root&&small);assert.equal(small.completed,false)
 assert.equal(phases.reduce((n:number,p:any)=>n+p.exclusiveUnits,0),root.units)
 return {source:pin,id:row.id,variant:row.variant,repetition:row.repetition,work:row.work,weights:data.weights,
  diagnosticUnits:root.units,generationQuarterEndpoint:row.work/4,phases,
  scope:'unchanged input and diagnostic all-one extras; not calibrated W, not a production generation-cap test'}
}
if(import.meta.main){
 const dir=process.argv[2]!,old15=process.argv[3]!,old50=process.argv[4]!,out=process.argv[5]
 const parse=(path:string)=>readFileSync(path,'utf8').split('\n').filter(l=>l.startsWith('ORIGINAL_PATH_CASE ')).map(l=>JSON.parse(l.slice(19)))
 const reports=[]
 for(const [job,work,rep,old]of [['epr-preflight-15m',15000000,1,old15],['epr-preflight-50m',50000000,2,old50]] as const){
  const rows=parse(join(dir,job+'.log')),prior=parse(join(old,'epr-original-'+rep+'.log'));assert.equal(rows.length,2)
  for(const row of rows){assert.equal(row.work,work);assert.equal(row.repetition,rep)
   reports.push(auditPreflight(row,prior.find(r=>r.variant===row.variant)))
   if(out){mkdirSync(out,{recursive:true});writeFileSync(join(out,`${work}-${row.variant}.json.gz`),Buffer.from(row.receiptGzipBase64,'base64'))}
  }
 }
 const result={passed:true,reports,scope:'phase attribution only; EPR was never reached'}
 if(out)writeFileSync(join(out,'summary.json'),JSON.stringify(result,null,2)+'\n')
 console.log('EPR_PREFLIGHT_PHASE_AUDIT '+JSON.stringify(result))
}
