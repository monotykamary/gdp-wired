import {readFileSync,readdirSync,writeFileSync} from 'node:fs'
const root=process.argv[2]??'runs/mldr-incl-safety-input',jobs:any[]=[],stages=readdirSync(root).filter(f=>f.startsWith('stage-')&&f.endsWith('.json')).map(file=>({file,d:JSON.parse(readFileSync(root+'/'+file,'utf8'))})).filter(({d})=>d.pass===1&&d.rawGoal&&d.certificateRequest?.reads?.length)
const seen=new Set<string>(),selected=stages.filter(({d})=>{const key=JSON.stringify([d.law,d.phase,d.hyps?.length]);if(seen.has(key))return false;seen.add(key);return true}).slice(0,24)
for(const {file}of selected)for(const mode of ['raw','preferred','keyed','seeded'])for(const ms of [250,1000,2700]){
 const name=`${file.slice(0,-5)}-${mode}-${ms}`
 jobs.push({name,cmd:`set -e; bash research/track-m/prepare-vendors.sh; bun install --frozen-lockfile >/dev/null; timeout -s KILL 30 bun research/mldr-incl/replay.ts inputs/${file} ${mode} ${ms}`,cpu:8,memory:14336,timeout:90})
}
if(!jobs.length)throw Error('no replayable stages');writeFileSync('research/mldr-incl/replay-jobs.json',JSON.stringify(jobs,null,2)+'\n');writeFileSync('runs/mldr-incl-replay-selection.json',JSON.stringify(selected.map(({file,d})=>({file,law:d.law,phase:d.phase,hyps:d.hyps?.length})),null,2)+'\n');console.log(JSON.stringify({stages:selected.length,jobs:jobs.length}))
