import {prepareFileCheck} from '../cli.ts'
import {withBudget} from '../../kernel/prove.ts'
import {completeWorkProfile} from '../work-profile.ts'
import {workLedger} from '../work-admission.ts'
import {exactRaw,workFromExact,workSub} from '../work-amount.ts'
import {parseRequest,refuse,Refusal,wireJSON} from './protocol.ts'
import {failure} from './service.ts'
import {sourceGuard,type WorkspaceRoot} from './workspace.ts'

// Module initialization only; this does not parse/load any workspace source.
export async function executeSource(args:unknown,roots:readonly WorkspaceRoot[]){
  const run=await prepareFileCheck()
  const before=workLedger.snapshot();let calls=0,sticky:Refusal|undefined
  let limits:ReturnType<typeof parseRequest>['budget']|undefined
  const budget=()=>{const after=workLedger.snapshot();return {limits:limits??null,apiCalls:calls,work:exactRaw(workSub(workFromExact(after.actual),workFromExact(before.actual))),counters:Object.fromEntries(Object.entries(after.counters).map(([k,v])=>[k,String(BigInt(v)-BigInt(before.counters[k as keyof typeof before.counters]))])),profile:completeWorkProfile.id,provisional:true,coverage:{counted:'Existing engine work sinks during synchronous extraction, law parsing, proofs, replay and proposals under one root budget and sticky refusal boundary.',notCounted:['module initialization','filesystem bytes/identity/hash operations','external interpreter runtime and project code execution','unmetered frontend parsing operations'],apiCalls:'Each extraction and each top-level proof/step/liveness/two-run invocation. Internal engine subcalls are covered by counted work, not separate API calls.',sourceBytesPerFile:131072,projectConfig:'disabled in initial workspace profile; no ancestor discovery or project interpreter overrides',clock:'counted logical telemetry and finite proposal candidate cap; no wall stop in the CLI proposal driver'}}}
  try{
    const q=parseRequest('check',args);limits=q.budget
    if(!completeWorkProfile.enabled)refuse('counted-profile-required','Start source workers with GDP_WORK_FULL=1 before engine imports.','Counted profile is disabled.')
    const invoke=<T>(f:()=>T):T=>{if(sticky)throw sticky;if(calls>=q.budget.apiCalls){sticky=new Refusal('api-budget-exceeded','Increase budget.apiCalls or check fewer entries/laws.','Source engine API allowance exhausted.');throw sticky}calls++;return f()}
    return withBudget(q.budget.work,()=>workLedger.withCapacityRefusalBoundary(()=>{
      const source=sourceGuard(roots,q.file!)
      let rules
      try{rules=run(source.file,source.root,{invoke,candidates:q.budget.candidates},source.guard)}catch(e){if(e instanceof Refusal)throw e;refuse('source-engine-refused','Inspect the exact extractor reason; use supported Python/plain TypeScript with explicit law comments.',e instanceof Error?e.message:String(e))}
      if(sticky)throw sticky
      const receipt=source.receipt()
      const laws=rules.flatMap(r=>r.laws)
      const label=rules.length>0&&rules.every(r=>r.ok)&&laws.length>0&&laws.every(l=>l.verdict==='proven')?'proven':laws.some(l=>l.verdict==='broken'&&l.run?.length)?'broken':'unknown'
      const output={schema:'gdp-wired/agent-tool/v1',tool:'check',ok:true,label,subject:receipt,result:{rules},...(label==='unknown'?{reason:'No complete checked proof set, no stated laws, or a source/law was refused; inspect rule refusals and law reasons.'}:{}),assumptions:{scope:'Existing CLI file extraction, model proof and native replay behavior; not an OS sandbox or a proof of every possible runtime behavior.',workspaceTrust:'Server-configured roots explicitly authorize runtime/project code execution, imports and dependencies. Mutable hostile workspaces require external OS isolation.',supported:['Python','plain TypeScript/JavaScript'],unsupported:['Effect','XState','other CLI languages','project gdp configuration overrides']},budget:budget()}
      // Serialization validation is inside the sticky boundary too. A caught refusal cannot escape as proof.
      wireJSON(output)
      return output
    }))
  }catch(e){return {...failure('check',e),label:'unknown',budget:budget()}}
}
