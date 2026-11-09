import {readFileSync,writeFileSync} from 'node:fs'
const ids=(file:string)=>[...new Set((JSON.parse(readFileSync(file,'utf8')) as {name:string}[]).map(j=>j.name.split('-s60-r')[0]!))]
const protocols=ids('research/track-p/ic3syn-paired-gate-jobs.json'),duoai=ids('research/track-p/duoai-paired-gate-jobs.json')
if(protocols.length!==29||duoai.length!==10)throw Error('unexpected gate roster')
for(const [kind,list,repeats] of [['ic3syn',protocols,3],['duoai',duoai,1],['broken',protocols,1]] as const){
 const jobs=list.flatMap((id,i)=>Array.from({length:repeats},(_,r)=>({name:`${id}-r${r+1}`,cmd:`bash research/mldr-incl/compare-main.sh ${kind} ${id} ${(i+r)%2?'base':'cand'}`,cpu:8,memory:14336,timeout:240,vm_type:'large',timing:true})))
 writeFileSync(`research/mldr-incl/${kind}-jobs.json`,JSON.stringify(jobs,null,2)+'\n');console.log(JSON.stringify({kind,jobs:jobs.length}))
}
