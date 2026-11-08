// Small deterministic verifier for the retained generation records.
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync} from 'node:fs'
const dir=process.argv[2]??'runs/track-gen-final-replays-v1'
type RecordRow={label:string,candidateCount:number,candidateHash:string,candidates:unknown[],wallMs:number,families:Record<string,{calls:number,ms:number,produced:number,retained:string[]}>}
const records:RecordRow[]=[]
let label=''
for(const line of readFileSync(`${dir}/generation-pairs.log`,'utf8').split('\n')){
 if(/^(GENERATION repeat=|PROFILE side=)/.test(line))label=line
 else if(line.startsWith('{"candidateCount"'))records.push({label,...JSON.parse(line)})
}
writeFileSync(`${dir}/records.json`,JSON.stringify(records)+'\n')
const expected='5e7acd1171d499bb2e2a21c326c0ca8013d98f8ab18c2bab9401d527de63e4e8'
if(records.length!==8)throw Error(`expected eight records, got ${records.length}`)
for(const r of records)if(r.candidateCount!==24||r.candidateHash!==expected||createHash('sha256').update(JSON.stringify(r.candidates)).digest('hex')!==expected)throw Error(`candidate drift: ${r.label}`)
const pairs=Array.from({length:3},(_,i)=>{
 const parent=records.find(r=>r.label===`GENERATION repeat=${i+1} side=parent`)!,candidate=records.find(r=>r.label===`GENERATION repeat=${i+1} side=candidate`)!
 if(!parent||!candidate||candidate.wallMs>=parent.wallMs)throw Error(`no reduction in pair ${i+1}`)
 return {repeat:i+1,parentMs:parent.wallMs,candidateMs:candidate.wallMs,ratio:candidate.wallMs/parent.wallMs,parentGenerationMs:parent.families.generation!.ms,candidateGenerationMs:candidate.families.generation!.ms}
})
const parent=records.find(r=>r.label==='PROFILE side=parent')!,candidate=records.find(r=>r.label==='PROFILE side=candidate')!
if(JSON.stringify(Object.keys(parent.families))!==JSON.stringify(Object.keys(candidate.families)))throw Error('generator roster changed')
const families=Object.keys(parent.families).map(name=>{
 const before=parent.families[name]!,after=candidate.families[name]
 if(!after||before.calls!==after.calls||before.produced!==after.produced||JSON.stringify(before.retained)!==JSON.stringify(after.retained))throw Error(`family changed: ${name}`)
 return {name,parentMs:before.ms,candidateMs:after.ms,produced:after.produced,retained:after.retained}
})
const average=(xs:number[])=>xs.reduce((a,b)=>a+b,0)/xs.length
const meanParentMs=average(pairs.map(p=>p.parentMs)),meanCandidateMs=average(pairs.map(p=>p.candidateMs))
const result={passed:true,candidates:24,candidateHash:expected,pairs,meanParentMs,meanCandidateMs,reduction:1-meanCandidateMs/meanParentMs,families}
writeFileSync(`${dir}/generation-verified.json`,JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify({...result,families:families.map(f=>({...f,retained:f.retained.length}))}))
