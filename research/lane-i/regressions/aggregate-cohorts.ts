// Combine only independently audited cohort receipts, never skip/result counts.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {summarize} from './merge-bisect-audit.ts'
const dirs=process.argv.slice(2),rows:any[]=[],issues:string[]=[],seen=new Set<string>()
for(const dir of dirs){const audit=JSON.parse(readFileSync(join(dir,'cohort-audit.json'),'utf8')),packed=readFileSync(join(dir,'accepted-summaries.json.gz'));if(audit.issues.length)issues.push(...audit.issues.map((s:string)=>dir+': '+s));if(createHash('sha256').update(packed).digest('hex')!==audit.acceptedSha256)throw new Error('derived receipt hash mismatch');for(const row of JSON.parse(gunzipSync(packed).toString('utf8'))){const key=row.revision+':'+row.replica;if(seen.has(key))throw new Error('duplicate cohort receipt '+key);seen.add(key);rows.push(row)}}
const output={issues,receipts:rows.length,byRevision:summarize(rows)}
writeFileSync(join(dirs[0]!,'aggregate-cohorts.json'),JSON.stringify(output,null,2)+'\n');console.log(JSON.stringify(output));if(issues.length)process.exitCode=1
