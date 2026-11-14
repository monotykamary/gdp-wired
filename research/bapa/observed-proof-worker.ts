import {parentPort,workerData} from 'node:worker_threads'
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {BudgetExpired,profile,proveLaws,setProveDump,withBudget} from '../../kernel/prove.ts'
import {checkGhostedLaws} from '../../kernel/kernel.ts'
import {functionInstanceProgress,withFunctionInstances} from '../../kernel/function-instances.ts'
import {withWorkAdmissionTrace,type WorkAdmissionEvent} from '../../core/work-admission.ts'
import {completeWorkProfile} from '../../core/work-profile.ts'
import {rigidMinimal,rigidMinimalLaw} from './rigid-minimal.ts'
import {rigidNaive} from './rigid-naive.ts'
import type {ObservedOptions} from './observed-proof.ts'
const o=workerData as ObservedOptions&{shared:SharedArrayBuffer,started:number}, counters=new BigInt64Array(o.shared), sites=new Map<string,number>()
let events=0,kernelCalls=0,observerFailures=0,wallExpired=false
const kernelEntries=new Set(['kernel choiceFree','kernel linear','kernel termId','kernel truth','kernel facts'])
const siteCounts=new Map<string,{events:number,charged:bigint}>()
let last:ReturnType<typeof functionInstanceProgress>
const deadline=o.started+o.wallMs
const publish=()=>{last=functionInstanceProgress()??last;if(last){Atomics.store(counters,1,BigInt(last.candidates));Atomics.store(counters,2,BigInt(last.generated));Atomics.store(counters,3,BigInt(last.matched));Atomics.store(counters,4,BigInt(last.work))}Atomics.store(counters,5,BigInt(kernelCalls));Atomics.store(counters,9,BigInt(profile.solves));Atomics.store(counters,10,BigInt(profile.nodes));Atomics.store(counters,11,BigInt(Date.now()))}
const observe=(e:WorkAdmissionEvent)=>{
  // An explicitly authorized cooperative wall budget, separate from telemetry.
  // It is diagnostic cancellation only, never a refutation or successful proof.
  if(Date.now()>=deadline){wallExpired=true;throw new BudgetExpired('diagnostic own wall budget')}
  try{
    events++;Atomics.store(counters,8,BigInt(events))
    if(e.kind==='start'){
      const site=e.site??e.sink??e.kind
      let id=sites.get(site);if(id===undefined){id=sites.size+1;sites.set(site,id);parentPort!.postMessage({event:'site',id,site})}
      Atomics.store(counters,0,BigInt(id))
      if(kernelEntries.has(site)) kernelCalls++
      const count=siteCounts.get(site)??{events:0,charged:0n};count.events++;count.charged+=BigInt(e.granted??'0');siteCounts.set(site,count)
      Atomics.store(counters,6,BigInt(e.counters.checkSteps))
      Atomics.store(counters,7,BigInt(e.actual.numerator)/BigInt(e.actual.denominator))
    }
    if(events%1024===0||e.kind==='refuse'||e.kind==='trace-end')publish()
  }catch{observerFailures++}
}
let terminal:Record<string,unknown>
try{
  if(!completeWorkProfile.enabled)throw Error('diagnostic full-work profile was not enabled before imports')
  const p=o.model==='naive'?rigidNaive():undefined, minimal=p?undefined:rigidMinimal(),machine=p?.machine??minimal!.abstractMachine,laws=p?.laws??[rigidMinimalLaw],strategy=p?.strategy??minimal!.functionInstances
  writeFileSync(join(o.out,'source-machine.json'),JSON.stringify({machine,laws,strategy,model:o.model},null,2)+'\n')
  profile.on=true
  setProveDump(goal=>{try{parentPort!.postMessage({event:'goal',goal:{name:goal.name,hyps:goal.hyps.length}})}catch{observerFailures++}})
  const result=withFunctionInstances(strategy,()=>withWorkAdmissionTrace(observe,()=>withBudget(o.units,()=>{
    const report=proveLaws(machine,laws)
    const ghostedChecked=!!p&&report.proven&&report.checked&&!!report.proof&&checkGhostedLaws(p.ghosted,laws,report.proof)
    publish();return {report,ghostedChecked}
  })))
  if(result.status==='complete'){
    const r=result.value.report,checked=r.checked&&(p?result.value.ghostedChecked:true)
    terminal={terminal:wallExpired?'wall-budget':r.proven&&checked?'proven':'returned-unknown',verdictReturned:!wallExpired,proven:!wallExpired&&r.proven,checked:!wallExpired&&checked,result,stats:result.stats}
  }else terminal={terminal:'function-search-limit',verdictReturned:true,proven:false,checked:false,result}
}catch(e){
  terminal={terminal:wallExpired?'wall-budget':e instanceof BudgetExpired?'work-budget':'error',verdictReturned:false,proven:false,checked:false,error:e instanceof Error?e.message:String(e),stats:last}
}finally{setProveDump(undefined);profile.on=false;try{publish()}catch{observerFailures++}}
terminal={...terminal,siteCounts:[...siteCounts].map(([site,c])=>({site,events:c.events,charged:String(c.charged)})).sort((a,b)=>b.events-a.events),siteCountMeaning:'metered start events and primitive amounts, not phase wall time',observerFailures,wallExpired,kernelCallsCoverage:'existing metered kernel choiceFree/linear/termId/truth/facts entry sites only',profile:{solves:profile.solves,nodes:profile.nodes,goals:profile.goals},helperClassification:o.model==='naive'?'GIVEN, not found':'none',groundSeed:'none',counted:false,accepted:false}
// Save in the worker before messaging the parent; the parent writes a second
// terminal envelope after joining, so either side can leave durable evidence.
writeFileSync(join(o.out,'worker-report.json'),JSON.stringify(terminal,null,2)+'\n')
parentPort!.postMessage({event:'terminal',report:terminal});parentPort!.close()
