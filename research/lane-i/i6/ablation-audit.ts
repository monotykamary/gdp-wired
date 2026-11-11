import {strict as a} from 'node:assert'
import {readFileSync,readdirSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {isDeepStrictEqual} from 'node:util'
const [dir,census,source]=process.argv.slice(2),keys3=['tableCells','checkSteps','cubeTests']
const read=(file:string,prefix:string)=>{const line=readFileSync(file,'utf8').split('\n').find(x=>x.startsWith(prefix));if(!line)return undefined;const env=JSON.parse(line.slice(prefix.length)),bytes=Buffer.from(env.gzipBase64,'base64');a.equal(createHash('sha256').update(bytes).digest('hex'),env.sha256);return JSON.parse(gunzipSync(bytes).toString())}
const old=(r:Record<string,number>)=>Object.fromEntries(Object.entries(r).filter(([k])=>!keys3.includes(k)))
const records:any[]=[],missing:string[]=[]
for(const file of readdirSync(dir!).filter(f=>f.endsWith('.log'))){const r=read(join(dir!,file),'I6_ABLATION_RECEIPT ');if(!r){missing.push(file);continue}a.equal(r.source,source);a.equal(r.clockReads,0);a.equal(r.schema,'i6-writer-ablation-v1');a.equal(r.diagnosticOnly,true);a.equal(r.sourceDigest,'1e2c9770632f3aeeadd36ea09f3f90cf169b06948abdeaf88bf0150a50d3f240');for(const [k,v]of Object.entries(r.raw)){a(Number.isSafeInteger(v)&&Number(v)>=0,k)}records.push(r)}
// Source digest is bound above independently of individual mode receipts.
const near=(x:number,y:number)=>Math.abs(x-y)<=Math.max(1e-6,Math.abs(x)*1e-11)
const summary=[]
for(const id of ['client_server_ae','simple_election']){
 const rows=records.filter(r=>r.id===id),get=(mode:string,w:number)=>rows.find(r=>r.mode===mode&&r.allowance===w),on=get('on',15000000),off=get('off',15000000),highOn=get('on',1e12),highOff=get('off',1e12),shadow=get('shadow',1e12)
 const before=read(join(census!,'strict-'+id+'.log'),'CANDIDATE_RECEIPT ')
 const reproduce=!!on&&isDeepStrictEqual(on.raw,before.searchRaw)&&near(on.chargedUnits,before.searchUnits)&&on.result.verdict===before.result.verdict
 if(on)a(reproduce,'writer-on reproduction '+id)
 if(highOff&&shadow){a.equal(shadow.semanticHash,highOff.semanticHash,'shadow result '+id);a.deepEqual(old(shadow.raw),old(highOff.raw),'shadow old work '+id);a(near(shadow.chargedUnits,highOff.chargedUnits),'shadow charge '+id);for(const key of keys3)a.equal(highOff.raw[key],0)}
 const describe=(r:any)=>r?{mode:r.mode,allowance:r.allowance,result:r.result,oldUnits:r.oldUnits,addedUnits:r.addedUnits,actualUnits:r.actualUnits,chargedUnits:r.chargedUnits,semanticHash:r.semanticHash,queryCount:r.queries.length,queries:r.queries.slice(-4).map((q:any)=>({kind:q.kind,goal:q.goal,status:q.status,why:q.why,depth:q.depth,chargedUnits:q.chargedUnits,oldUnits:q.oldUnits,clock:q.clock,deadline:q.deadline,budgetEnd:q.budgetEnd})),crossings:r.crossings.slice(-8).map((p:any)=>({clock:p.clock,deadline:p.deadline,deadlineRawUnits:p.deadline*250,deadlineDeltaUnits:p.deadline*250-(p.clock*250-p.chargedUnits),oldUnits:p.oldUnits,addedUnits:p.chargedUnits-p.oldUnits,oldBelowEndpoint:p.oldUnits<=p.deadline*250-(p.clock*250-p.chargedUnits),lastQuery:p.lastQuery,lastEvent:p.lastEvent}))}:null
 const pair=(left:any,right:any)=>left&&right?{sameResult:left.semanticHash===right.semanticHash,sameOldRaw:isDeepStrictEqual(old(left.raw),old(right.raw)),leftResult:left.result.verdict,rightResult:right.result.verdict}:null
 summary.push({id,onReproducesStrictCensus:reproduce,shadowVsOffLifted:pair(shadow,highOff),onVsOffLifted:pair(highOn,highOff),rows:[on,off,highOn,highOff,shadow].map(describe)})
}
console.log('I6_ABLATION_AUDIT '+JSON.stringify({source,records:records.length,missing,allZeroClockReads:true,diagnosticOnly:true,summary}))
if(records.length!==10||missing.length)process.exitCode=1
