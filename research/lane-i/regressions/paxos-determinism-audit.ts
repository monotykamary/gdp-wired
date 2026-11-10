// Compare exact completed counters separately from wall-censored unknown totals.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const [output,...dirs]=process.argv.slice(2)
if(!output||!dirs.length)throw Error('usage: paxos-determinism-audit.ts output.json audited-dir ...')
const expectedBase='b09da82d9ada6e0cdc31f943292cfea727f5752e',expectedCandidate='bf01190119f9409077a36e11a4a5b763fb6c1cad'
const groups=new Map<string,any[]>(),issues:string[]=[]
for(const dir of dirs){
 const checked=JSON.parse(readFileSync(join(dir,'cohort-audit.json'),'utf8')),bytes=readFileSync(join(dir,'accepted-summaries.json.gz'))
 if(checked.issues.length||createHash('sha256').update(bytes).digest('hex')!==checked.acceptedSha256)throw Error('unqualified or altered cohort: '+dir)
 for(const row of JSON.parse(gunzipSync(bytes).toString())){
  if(row.baseline!==expectedBase||row.revision!==expectedCandidate||row.strictMs!==60000)throw Error('source/budget mismatch')
  for(const record of row.records){
   if(['base','candidate'].some(side=>record.outcomes[side].exit!==0||record.outcomes[side].results.length!==1)){issues.push(dir+': incomplete child');continue}
   const samples=groups.get(row.cpu)??[];samples.push({replica:row.replica,repeat:record.repeat,outcomes:record.outcomes});groups.set(row.cpu,samples)
  }
 }
}
const normalized=(attempt:any)=>({law:attempt.law,pass:attempt.pass,family:attempt.family,outcome:attempt.outcome,work:attempt.work,full:Math.round(attempt.full*1e6)/1e6})
const unique=(xs:unknown[])=>new Set(xs.map(x=>JSON.stringify(x))).size
const selected=[...groups].filter(([,rows])=>rows.length>=3).map(([cpu,rows])=>({cpu,rows:rows.slice(0,3)}))
const samples=selected.flatMap(group=>group.rows)
const commonPrefix=(side:string)=>{const arrays=samples.map(row=>row.outcomes[side].attempts.map(normalized));if(!arrays.length)return[];const first=arrays[0],out=[];for(let i=0;i<Math.min(...arrays.map(a=>a.length));i++){if(unique(arrays.map(a=>a[i]))!==1)break;out.push(first[i])}return out}
const prefixes={base:commonPrefix('base'),candidate:commonPrefix('candidate')}
let divergence:number|null=null
for(let i=0;i<Math.min(prefixes.base.length,prefixes.candidate.length);i++)if(JSON.stringify(prefixes.base[i])!==JSON.stringify(prefixes.candidate[i])){divergence=i;break}
const totals=(side:string)=>samples.map(row=>{const result=row.outcomes[side].results[0].search;return{verdict:result.verdict,work:result.work,full:result.full}})
const baseTotals=totals('base'),candidateTotals=totals('candidate')
const complete=issues.length===0&&selected.length>=2
const result={issues,complete,source:{baseline:expectedBase,candidate:expectedCandidate},models:selected.map(group=>({cpu:group.cpu,samples:group.rows.map(row=>({replica:row.replica,repeat:row.repeat,base:row.outcomes.base.results[0].search,candidate:row.outcomes.candidate.results[0].search}))})),exactFinalCounters:{baseIdentical:unique(baseTotals)===1,candidateIdentical:unique(candidateTotals)===1,base:baseTotals,candidate:candidateTotals},determinismEstablished:complete&&unique(baseTotals)===1&&unique(candidateTotals)===1,completedAttemptPrefix:{roundingDigits:6,baseLength:prefixes.base.length,candidateLength:prefixes.candidate.length,firstDivergence:divergence===null?null:{index:divergence,base:prefixes.base[divergence],candidate:prefixes.candidate[divergence]}},scope:'Censored final counts are not deterministic proof costs. Prefix comparison omits wall time and rounds fractional full units only; raw final counts are exact.',finalGate:false}
writeFileSync(output,JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify({...result,models:result.models.map(m=>({cpu:m.cpu,samples:m.samples.length})),exactFinalCounters:{baseIdentical:result.exactFinalCounters.baseIdentical,candidateIdentical:result.exactFinalCounters.candidateIdentical}}))
if(!complete)process.exitCode=1
