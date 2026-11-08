// Fixed family, exact production attempt implementation, unchanged per-goal cap.
import {readFileSync} from 'node:fs'
import {gzipSync} from 'node:zlib'
import {type Law,type Machine} from '../../core/machine.ts'
import {countedAttempts,countsDump,certFor,cprof} from '../../core/counts.ts'
import {checkMC,checkCountedLaws,countedObligations,mcGoal} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,grow,withWall,withDeadline} from '../../kernel/prove.ts'
import {cdclStats} from '../../kernel/cdcl.ts'
import {readTuples} from '../../core/count-support.ts'
const data=JSON.parse(readFileSync(process.argv[2]!+'/family.json','utf8')) as {machine:Machine,laws:Law[]},m=data.machine,indices=[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74],laws=indices.map(i=>data.laws[i]!),targets=process.argv.slice(3).map(Number),rows:object[]=[],proofs:object[]=[],failures:object[]=[]
const milliseconds=1500;cdclStats.on=process.env.PROFILE==='1'
for(const index of targets.length?targets:indices){
 const law=data.laws[index]!,started=performance.now(),events:object[]=[],before={...cprof},cdclBefore={...cdclStats}
 let firstFailure:object|undefined,lastFailure:object|undefined
 countsDump.on=(event:object)=>{const e=event as Record<string,any>;if(e.rawGoal?.hyps.length>2&&e.certificateRequest){const copy=JSON.parse(JSON.stringify({index,phase:e.phase,raw:e.rawGoal,decls:e.decls,certificateRequest:e.certificateRequest,instances:e.instances,hyps:e.hyps,generation:e.generation}));firstFailure??=copy;lastFailure=copy}events.push({phase:e.phase,pass:e.pass,hyps:e.hyps?.length,rawHyps:e.rawGoal?.hyps?.length,insts:e.certificateRequest?.insts?.length,generation:e.generation})}
 const result=withWall(performance.now()+2500,()=>counted(fullRate,()=>{
  const until=clock()+milliseconds,runner=countedAttempts(m,[],new Set(laws),until),countFirst=process.env.GDP_COUNTS_COUNT_FIRST==='1'&&readTuples(law.holds).some(([map])=>!!m.counts?.[map])
  return withDeadline(until,()=>{
   let answer=runner.traced(law,laws,countFirst?1:0,Math.max(0,until-clock()))
   if(!('proof'in answer)&&(countFirst||runner.counted)&&clock()<until)answer=runner.traced(law,laws,countFirst?0:1,Math.max(0,until-clock()))
   return answer
  })
 },true))
 const elapsed=performance.now()-started
 if(!('proof'in result))failures.push({index,first:firstFailure,last:lastFailure})
 if('proof'in result){
  const goals=countedObligations(m,laws,{[law.name]:result.proof.instances},laws.indexOf(law)),checks=goals.map(({goal,decls})=>checkMC(goal.hyps,decls,result.proof.certs[goal.name]!))
  if(checks.some(c=>!c))throw Error('production attempt returned unchecked proof')
  rows.push({index,phase:'step',status:'tree',checked:checks.at(-1),ms:elapsed,events,cprof:Object.fromEntries(Object.entries(cprof).map(([k,v])=>[k,v-(before[k]??0)])),cdcl:Object.fromEntries(Object.entries(cdclStats).filter(([,v])=>typeof v==='number').map(([k,v])=>[k,Number(v)-Number((cdclBefore as any)[k]??0)]))})
  proofs.push({index,proof:result.proof})
 }else rows.push({index,phase:'step',status:result.stuck,checked:false,ms:elapsed,events,cprof:Object.fromEntries(Object.entries(cprof).map(([k,v])=>[k,v-(before[k]??0)])),cdcl:Object.fromEntries(Object.entries(cdclStats).filter(([,v])=>typeof v==='number').map(([k,v])=>[k,Number(v)-Number((cdclBefore as any)[k]??0)]))})
 const init=withWall(performance.now()+2500,()=>counted(fullRate,()=>withDeadline(clock()+milliseconds,()=>{
  const {goal,decls}=countedObligations(m,laws,{},laws.indexOf(law))[0]!,cert=certFor(goal,decls,false,10),gg=mcGoal(goal.hyps,decls,cert);if(!gg)return {status:'invalid',checked:false}
  const r=grow(gg,new Map(),{nodes:0,until:clock()+milliseconds});return 'tree'in r?{status:'tree',checked:checkMC(goal.hyps,decls,{...cert,tree:r.tree})}:{status:r.stuck,checked:false}
 }),true));rows.push({index,phase:'init',...init});console.log(JSON.stringify(rows.at(-2)));console.log(JSON.stringify(rows.at(-1)))
}
countsDump.on=undefined
const complete=targets.length===0&&proofs.length===laws.length,closedFamily=complete&&checkCountedLaws(m,laws,{instances:Object.fromEntries(proofs.map((p:any)=>[data.laws[p.index]!.name,p.proof.instances])),certs:Object.assign({},...proofs.map((p:any)=>p.proof.certs))})
if(complete&&!closedFamily)throw Error('the full fixed-family proof did not check')
console.log(JSON.stringify({kind:'summary',checked:rows.filter((r:any)=>r.checked).length,total:rows.length,closedFamily,rows}));console.log('PROOFS_GZIP '+gzipSync(JSON.stringify(proofs)).toString('base64'));console.log('FAILURES_GZIP '+gzipSync(JSON.stringify(failures)).toString('base64'))
