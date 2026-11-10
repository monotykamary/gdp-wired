import {readFileSync,readdirSync,writeFileSync,mkdirSync} from 'node:fs'
import {dirname} from 'node:path'
const root=process.argv[2]??'runs/mldr-incl-safety-input',fixture=process.argv[3]??'research/mldr-incl/fixtures/safety-gp1.br',out=process.argv[4]??'research/mldr-incl/replay-jobs.json',sample=Number(process.argv[5]??0),jobs:any[]=[]
const stages=readdirSync(root).filter(f=>f.startsWith('stage-')&&f.endsWith('.json')).map(file=>({file,d:JSON.parse(readFileSync(root+'/'+file,'utf8'))})).filter(({d})=>d.pass===1&&d.rawGoal&&d.certificateRequest?.reads?.length)
const seen=new Set<string>(),unique=stages.sort((a,b)=>Number(a.file.match(/-(\d+)\.json$/)?.[1]??0)-Number(b.file.match(/-(\d+)\.json$/)?.[1]??0)).filter(({d})=>{const key=JSON.stringify([d.rawGoal,d.instances,d.certificateRequest]);if(seen.has(key))return false;seen.add(key);return true}).slice(0,24)
if(!Number.isInteger(sample)||sample<0)throw Error('invalid sample count')
const positions=sample>0&&sample<unique.length?new Set(Array.from({length:sample},(_,i)=>sample===1?unique.length-1:Math.round(i*(unique.length-1)/(sample-1)))):undefined
const selected=unique.filter((_,i)=>!positions||positions.has(i))
for(const {file}of selected)for(const mode of ['raw','preferred','keyed','seeded'])for(const ms of [250,1000,2700]){
 const name=`${file.slice(0,-5)}-${mode}-${ms}`
 jobs.push({name,cmd:`set -e; bash research/track-m/prepare-vendors.sh; bun install --frozen-lockfile >/dev/null; timeout -s KILL 30 bun research/mldr-incl/replay.ts ${fixture}#${file} ${mode} ${ms}`,cpu:8,memory:14336,vm_type:'large',timeout:90})
}
if(!jobs.length)throw Error('no replayable stages');mkdirSync(dirname(out),{recursive:true});writeFileSync(out,JSON.stringify(jobs,null,2)+'\n');writeFileSync(out+'.selection.json',JSON.stringify(selected.map(({file,d})=>({file,law:d.law,phase:d.phase,hyps:d.hyps?.length})),null,2)+'\n');console.log(JSON.stringify({fixture,out,stages:selected.length,jobs:jobs.length}))
