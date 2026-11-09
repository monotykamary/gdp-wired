import {readFileSync,writeFileSync} from 'node:fs'
type Job={name:string,cmd:string,cpu:number,memory:number,timeout:number,vm_type?:string}
const jobs=[1,2,3].flatMap(i=>(JSON.parse(readFileSync(`research/track-gen/ic3syn-r${i}-jobs.json`,'utf8')) as Job[]).filter(j=>!j.name.startsWith('paxos_epr-')).map(source=>{if(!source.cmd.includes("--skip 'broken'"))throw Error(`missing phase ${source.name}`);return {...source,name:`negative-${source.name}`,cmd:source.cmd.replaceAll("--skip 'broken'","--skip 'search'"),cpu:8,memory:14336,vm_type:'large'}}))
if(jobs.length!==84)throw Error(`expected 84 non-Paxos pairs, got ${jobs.length}`)
writeFileSync('research/track-gen/negative-suite-jobs.json',JSON.stringify(jobs,null,2)+'\n')
console.log(JSON.stringify({jobs:jobs.length,plusSeparatePaxos:3,ms:60000,baseline:'6a3874d3'}))
