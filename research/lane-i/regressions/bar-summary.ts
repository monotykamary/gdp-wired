// Interpret process completeness separately from answers printed before a child stops.
import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const dir=process.argv[2];if(!dir)throw new Error('bar output directory required')
const audit=JSON.parse(readFileSync(join(dir,'receipt-audit.json'),'utf8'))
if(audit.issues.length)throw new Error('resolve receipt integrity issues first')
const jobs:{name:string}[]=JSON.parse(readFileSync(join(import.meta.dir,'bar.jobs.json'),'utf8'))
type Child={answer:string,exit:number|null,signal?:string|null,error?:string,wallMs:number}
type Row={index:number,repeat:number,view:string,task:string,cpu:string,outcomes:Record<'base'|'candidate',Child>}
const rows:Row[]=[],sources:Record<string,string>={}
for(const job of jobs){
 const plain=join(dir,job.name+'.log'),gz=plain+'.gz',text=existsSync(gz)?gunzipSync(readFileSync(gz)).toString('utf8'):readFileSync(plain,'utf8')
 sources[job.name]=createHash('sha256').update(text).digest('hex')
 for(const line of text.split('\n'))if(line.startsWith('BAR_PAIR ')){
  const row=JSON.parse(line.slice(9)) as Row
  for(const side of ['base','candidate'] as const){const child=row.outcomes[side];row.outcomes[side]={answer:child.answer,exit:child.exit,signal:child.signal,error:child.error,wallMs:child.wallMs}}
  rows.push(row)
 }
}
if(rows.length!==audit.pairs.length)throw new Error('summary cardinality differs from audited receipts')
const completePairs=rows.filter(row=>row.outcomes.base.exit===0&&row.outcomes.candidate.exit===0)
const completeDifferences=completePairs.filter(row=>row.outcomes.base.answer!==row.outcomes.candidate.answer)
const partialAnswers=rows.flatMap(row=>(['base','candidate'] as const).flatMap(side=>{const child=row.outcomes[side];return child.exit!==0&& !['error','timeout'].includes(child.answer)?[{index:row.index,repeat:row.repeat,side,...child}]:[]}))
const processErrors:Record<string,number>={}
for(const row of rows)for(const side of ['base','candidate'] as const){const child=row.outcomes[side];if(child.error)processErrors[child.error]=(processErrors[child.error]??0)+1}
const report={baseline:audit.baseline,candidate:audit.candidate,batch:audit.batch,pairs:rows.length,completePairs:completePairs.length,completeDifferences,partialAnswers,processErrors,sources,rows,scope:'Diagnostic only. A parsed answer from an incomplete child is not a successful benchmark run or a final no-loss gate.'}
writeFileSync(join(dir,'summary.json'),JSON.stringify(report,null,2)+'\n')
console.log(JSON.stringify({pairs:rows.length,completePairs:completePairs.length,completeDifferences,partialAnswers:partialAnswers.length,processErrors}))
