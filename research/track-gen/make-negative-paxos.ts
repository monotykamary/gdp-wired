import {readFileSync,writeFileSync} from 'node:fs'
type Job={name:string,cmd:string,cpu:number,memory:number,timeout:number,vm_type?:string}
const jobs=[1,2,3].map(i=>{const source=(JSON.parse(readFileSync(`research/track-gen/ic3syn-r${i}-jobs.json`,'utf8')) as Job[]).find(j=>j.name===`paxos_epr-s60-r${i}`);if(!source||!source.cmd.includes("--skip 'broken'"))throw Error(`missing source pair ${i}`);return {...source,name:`negative-paxos-r${i}`,cmd:source.cmd.replaceAll("--skip 'broken'","--skip 'search'"),cpu:8,memory:14336,vm_type:'large'}})
writeFileSync('research/track-gen/negative-paxos-jobs.json',JSON.stringify(jobs,null,2)+'\n')
console.log(JSON.stringify({jobs:jobs.length,ms:60000,baseline:'6a3874d3'}))
