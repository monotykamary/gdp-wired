import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const [dir,jobsPath,revision]=process.argv.slice(2)
if(!dir||!jobsPath||!revision)throw Error('usage: summarize.ts dir jobs.json revision')
const read=(p:string)=>JSON.parse(readFileSync(p,'utf8')),jobs=read(jobsPath),backend=read(join(dir,'backends.json')),placement=read(join(dir,'placement.json'))
const statuses=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t')),issues:string[]=[],results:any[]=[]
if(statuses.length!==jobs.length||new Set(statuses.map(row=>row[0])).size!==jobs.length)issues.push('roster mismatch')
if(backend.where?.boat!==jobs.length||backend.fallbacks?.length)issues.push('not all on boat')
for(const job of jobs){
 const text=readFileSync(join(dir,job.name+'.log'),'utf8'),status=statuses.find(row=>row[0]===job.name),sources=text.split('\n').filter(line=>line.startsWith('PAXOS_FIX_SOURCE ')).map(line=>JSON.parse(line.slice(17)))
 if(sources.length!==1||sources[0].meta.revision!==revision||!sources[0].meta.clean)issues.push(job.name+': source identity')
 if(!placement[job.name]?.exclusive||placement[job.name].co_tenants!==0)issues.push(job.name+': placement')
 if(status?.[1]!=='0'||status?.[3]!=='boat')issues.push(job.name+': process exit '+status?.[1])
 if(!text.includes('PAXOS_FIX_VALIDATION_PASS shard-'))issues.push(job.name+': no terminal success marker')
 const sum=(re:RegExp)=>[...text.matchAll(re)].reduce((n,m)=>n+Number(m[1]),0)
 const passed=sum(/^\s*(\d+) pass\s*$/gm),failed=sum(/^\s*(\d+) fail\s*$/gm),skipped=sum(/^\s*(\d+) skip\s*$/gm),assertions=sum(/^\s*(\d+) expect\(\) calls\s*$/gm),failedTests=[...new Set(text.split('\n').filter(line=>line.startsWith('(fail)')))]
 if(failed)issues.push(job.name+': '+failed+' failed tests')
 results.push({name:job.name,exit:Number(status?.[1]),passed,failed,skipped,assertions,failedTests})
}
const sum=(key:string)=>results.reduce((n,row)=>n+row[key],0),result={revision,issues,passed:sum('passed'),failed:sum('failed'),skipped:sum('skipped'),assertions:sum('assertions'),results,qualified:issues.length===0,finalGate:false}
writeFileSync(join(dir,'suite-audit.json'),JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify(result));if(issues.length)process.exitCode=1
