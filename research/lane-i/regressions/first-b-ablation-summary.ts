import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {verifyTrace} from './receipt-audit.ts'
const [dir,jobsFile]=process.argv.slice(2);if(!dir||!jobsFile)throw new Error('usage: first-b-ablation-summary.ts dir jobs')
const jobs=JSON.parse(readFileSync(jobsFile,'utf8')),placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8')),issues:string[]=[],rows:any[]=[]
for(const job of jobs){const identity=/ablation\.ts (\d+) ([a-z-]+)/.exec(job.cmd);if(!identity)throw new Error('bad job');const text=readFileSync(join(dir,job.name+'.log'),'utf8'),found=text.split('\n').filter(line=>line.startsWith('FIRST_B_ABLATION ')).map(line=>JSON.parse(line.slice(17)))
 if(found.length!==2)issues.push(job.name+': expected two repeats')
 for(const row of found){if(row.group!==Number(identity[1])||row.mode!==identity[2]||row.cpu!==placement[job.name]?.cpu||row.strictMs!==60000||row.meta.base.revision!=='b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c'||row.meta.candidate.revision!=='1fc01c10f4fe5ee71101639cca55c5da39c3e10c')issues.push(job.name+': identity mismatch')
  const outcomes:Record<string,unknown>={}
  for(const [variant,o]of Object.entries(row.outcomes) as [string,any][]){issues.push(...verifyTrace(o).map(issue=>job.name+': '+issue));const raw=gunzipSync(Buffer.from(o.traceGzipBase64,'base64')).toString('utf8').split('\n---stderr---\n')[0]!,results=raw.split('\n').flatMap(line=>{try{const r=JSON.parse(line);return r.id==='consensus_forall'?[r]:[]}catch{return[]}});if(JSON.stringify(results)!==JSON.stringify(o.results))issues.push(job.name+': semantic trace mismatch');outcomes[variant]={exit:o.exit,signal:o.signal,search:o.results?.[0]?.search}}
  rows.push({mode:row.mode,group:row.group,repeat:row.repeat,cpu:row.cpu,outcomes})
 }
}
const output={issues,rows,scope:'Proposal-only ablation screening; not five-repeat Ryzen qualification.'};writeFileSync(join(dir,'ablation-summary.json'),JSON.stringify(output,null,2)+'\n');console.log(JSON.stringify({issues,rows:rows.map(row=>({...row,outcomes:Object.fromEntries(Object.entries(row.outcomes).map(([key,value])=>{const o=value as any;return[key,{exit:o.exit,verdict:o.search?.verdict,work:o.search?.work,full:o.search?.full,ms:o.search?.ms}]}))}))}));if(issues.length)process.exitCode=1
