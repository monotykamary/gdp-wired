// Manifest construction only. All verification processes run on boat.
import {readFileSync,writeFileSync} from 'node:fs'
type Job={name:string,cmd:string,cpu:number,memory:number,timeout:number,vm_type?:string}
const load=(file:string):Job[]=>JSON.parse(readFileSync(`research/track-gen/${file}`,'utf8'))
const ic3=[1,2,3].flatMap(i=>load(`ic3syn-r${i}-jobs.json`))
const first=ic3.filter(j=>j.name.startsWith('paxos_epr-')),rest=ic3.filter(j=>!j.name.startsWith('paxos_epr-'))
const tagged=(suite:string,jobs:Job[])=>jobs.map(j=>({...j,name:`${suite}-${j.name}`,cpu:8,memory:14336,vm_type:'large'}))
const jobs:Job[]=[...load('final-check-jobs.json'),...tagged('ic3',[...first,...rest]),...tagged('duo',load('duoai-jobs.json')),...tagged('broken',load('broken-jobs.json')),
 ...load('final-replays-jobs.json').filter(j=>j.name!=='check-and-tests'),
 ...Array.from({length:7},(_,i)=>({name:`shard-${i+1}-of-7`,cmd:`set -e; bash research/track-m/prepare-vendors.sh; bun install --frozen-lockfile >/dev/null; bun scripts/test-shards.ts --shard ${i+1}/7`,cpu:8,memory:14336,timeout:900}))]
if(jobs.length!==136||new Set(jobs.map(j=>j.name)).size!==136)throw Error('acceptance manifest cardinality')
writeFileSync('research/track-gen/acceptance-jobs.json',JSON.stringify(jobs,null,2)+'\n')
console.log(JSON.stringify({jobs:jobs.length,ic3:ic3.length,duo:10,broken:29,shards:7,baseline:'6a3874d3'}))
