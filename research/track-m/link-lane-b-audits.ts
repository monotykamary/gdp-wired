// Link checker-only output to exact named receipt arms. Not a final gate.
import {readFileSync,writeFileSync} from 'node:fs'
import {join,basename} from 'node:path'
import {createHash} from 'node:crypto'
import {strict as assert} from 'node:assert'
const lexical=(a:string|undefined,b:string|undefined)=>(a??'').localeCompare(b??'')
const [file,dir]=process.argv.slice(2);if(!file||!dir)throw Error('SUMMARY AUDIT_DIR required')
const summary=JSON.parse(readFileSync(file,'utf8')),records=new Map<string,any>()
for(const [name,exit]of readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t'))){
 assert(name);assert.equal(Number(exit),0)
 const path=join(dir,name+'.log'),text=readFileSync(path,'utf8'),logSha256=createHash('sha256').update(text).digest('hex');let input:string|undefined
 for(const line of text.split('\n')){
  if(line.startsWith('INPUT=')){input=basename(line.slice(6));continue}
  let r:any;try{r=JSON.parse(line)}catch{continue}
  if(r.conditional!==true)continue
  assert(input&&input.endsWith('.json.gz'));assert(!records.has(input));records.set(input,{...r,sourceLog:path,logSha256})
 }
}
const expected:string[]=summary.rows.flatMap((row:any)=>row.arms.map((arm:any)=>`${row.name}-${arm.side}.json.gz`))
assert.deepEqual([...records.keys()].sort(lexical),expected.sort(lexical))
for(const row of summary.rows)for(const arm of row.arms){
 const r=records.get(`${row.name}-${arm.side}.json.gz`);assert(r)
 for(const key of ['tag','law','units','wallMs'])assert.deepEqual(r[key],arm[key])
 assert.equal(r.checked,arm.workerChecked)
 arm.audit={sourceLog:r.sourceLog,logSha256:r.logSha256,conditional:true,checked:r.checked}
}
summary.independentAuditPending=false;summary.gateGreen=false
summary.independentAudit={outcomes:records.size,checked:[...records.values()].filter(r=>r.checked).length,unknown:[...records.values()].filter(r=>!r.checked).length}
writeFileSync(file,JSON.stringify(summary,null,2)+'\n');console.log(JSON.stringify(summary.independentAudit))
