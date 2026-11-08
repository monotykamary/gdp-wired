// Receipt verification only; this does not run any prover.
import {readFileSync,writeFileSync,mkdirSync,copyFileSync} from 'node:fs'
const root=process.argv[2]??'runs/track-gen-final-direct-v1'
const jobs:{name:string}[]=JSON.parse(readFileSync('research/track-gen/acceptance-jobs.json','utf8'))
const rows=new Map(readFileSync(`${root}/summary.tsv`,'utf8').trim().split('\n').map(l=>{const [name,exit,seconds,where]=l.split('\t');return [name!,{exit:Number(exit),seconds:Number(seconds),where}] as const}))
const placement=JSON.parse(readFileSync(`${root}/placement.json`,'utf8'))
const errors:string[]=[]
if(rows.size!==jobs.length)errors.push(`expected ${jobs.length} receipts, got ${rows.size}`)
for(const {name}of jobs){
 const row=rows.get(name),p=placement[name]
 if(!row||row.exit!==0||row.where!=='boat')errors.push(`${name}: missing, failed, or not boat`)
 if(!p||p.type!=='large'||p.vcpus!==8||!p.exclusive||p.co_tenants!==0)errors.push(`${name}: wrong or nonexclusive placement`)
 for(const [prefix,suite]of [['ic3-','ic3syn'],['duo-','duoai'],['broken-','broken']]as const)if(name.startsWith(prefix)){
  mkdirSync(`${root}/${suite}`,{recursive:true});copyFileSync(`${root}/${name}.log`,`${root}/${suite}/${name.slice(prefix.length)}.log`)
 }
}
const result={passed:errors.length===0,jobs:jobs.length,baseline:'6a3874d3',errors,shards:[...rows].filter(([name])=>name.startsWith('shard-')).map(([name,row])=>({name,...row}))}
writeFileSync(`${root}/receipt-checks.json`,JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result))
if(errors.length)process.exitCode=1
