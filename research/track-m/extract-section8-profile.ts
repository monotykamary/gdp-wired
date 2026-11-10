import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const [file,dir]=process.argv.slice(2);if(!file||!dir)throw new Error('LOG OUTPUT_DIR required')
const summaries:any[]=[]
for(const line of readFileSync(file,'utf8').split('\n')){
 if(!line.startsWith('{'))continue
 const r=JSON.parse(line)
 if(r.encoding!=='gzip-base64'||!/^tf(?:1|23|4)-(?:control|deferred|sliced|incremental)\.log$/.test(r.artifact))continue
 const text=gunzipSync(Buffer.from(r.data,'base64')).toString('utf8');writeFileSync(join(dir,r.artifact),text)
 for(const s of text.split('\n'))if(s.startsWith('{')){const row=JSON.parse(s);if(row.mode==='phase-census')summaries.push({artifact:r.artifact,law:row.law,checked:row.checked,proven:row.proven,wallMs:row.wallMs,countedUnits:row.countedUnits,kernelMs:row.phases.kernel,checkCalls:row.checkCalls,sites:Object.fromEntries(Object.entries(row.sites).filter(([k])=>/checkMC|kernel.ts:check$/.test(k))),detail:row.t1});else if(row.test?.startsWith('T-F'))summaries.push(row)}
}
writeFileSync(join(dir,'results.json'),JSON.stringify(summaries,null,2)+'\n')
console.log(JSON.stringify(summaries.map(({detail,...r})=>({...r,...(detail?{kernelChecks:detail.checks,kernelBucket:detail.buckets.kernel}:{} )})),null,2))
