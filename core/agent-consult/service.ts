import {proveLaws,proveStepLaws,withBudget} from '../../kernel/prove.ts'
import {search,interpret,type Machine,type Law} from '../../core/machine.ts'
import {inferLaws} from '../../core/infer.ts'
import {refinement,agree} from '../../core/compose.ts'
import {completeWorkProfile} from '../../core/work-profile.ts'
import {workLedger,BudgetExpired} from '../../core/work-admission.ts'
import {exactRaw,workFromExact,workSub} from '../../core/work-amount.ts'
import {Refusal,refuse,parseRequest,revision,type Request,type Unit} from './protocol.ts'

type Proof = {proven:boolean,checked:boolean,status:string,goal?:string,why?:string,witness?:unknown}
type RawProof = {proven:boolean,checked:boolean,failed?:{goal?:string,stuck?:string,witness?:unknown,why?:string}}
export function proofSummary(v:RawProof):Proof {return {proven:v.proven===true,checked:v.checked===true,status:v.proven===true&&v.checked===true?'proven':v.proven?'unchecked':'not-proven',...(v.failed?{goal:v.failed.goal,why:v.failed.why??v.failed.stuck,...(v.failed.witness?{witness:v.failed.witness}:{})}:{})}}
const counterDelta=(before:ReturnType<typeof workLedger.snapshot>,after:ReturnType<typeof workLedger.snapshot>)=>Object.fromEntries(Object.entries(after.counters).map(([k,v])=>[k,String(BigInt(v)-BigInt(before.counters[k as keyof typeof before.counters]))]))
const source=(l:Law)=>`import type {Law} from 'gdp-wired/machine'\nconst law: Law = ${JSON.stringify(l)}\n`
const binding=(u:Unit,laws:Law[])=>({unit:u.unit,revision:revision(u,laws)})
export function failure(tool:string,e:unknown){const r=e instanceof Refusal?e:e instanceof BudgetExpired?new Refusal('work-budget-exceeded','Increase budget.work within the published cap, or check fewer laws.','The counted work allowance was exhausted.'):e instanceof RangeError?new Refusal('numeric-range-refused','Keep runtime arithmetic within nonnegative safe integers; use a separately validated bigint surface for larger values.',e.message):new Refusal('engine-refused','Use the supported scalar AST; inspect the exact engine message and reduce/split the request.',e instanceof Error?e.message:String(e));return {schema:'gdp-wired/agent-tool/v1',tool,ok:false,refusal:{code:r.code,message:r.message,fix:r.fix},explanation:`${tool} refused: ${r.message} Fix: ${r.fix}`}}
const context=(q:Request)=>({domain:'scalar naturals; sub is truncated subtraction',scope:'model laws from the declared initial state under pre and request assumptions; not native conformance',subjects:[q.subject,q.before,q.after].filter((u):u is Unit=>u!==undefined).map(u=>({...binding(u,q.laws??[]),initial:u.rule.state,pre:u.rule.pre??null,requestAssumption:u.rule.assume??null})),laws:q.laws??[]})
export function execute(tool:unknown,args:unknown){
  const before=workLedger.snapshot();let calls=0,request:Request|undefined
  const invoke=<T>(f:()=>T):T=>{if(!request||calls>=request.budget.apiCalls)refuse('api-budget-exceeded','Increase budget.apiCalls or request fewer laws/candidates.','No further engine calls are admitted.');calls++;return f()}
  try {
    request=parseRequest(tool,args)
    if(request.tool==='status')refuse('status-registry-required','Call status through the stdio server that observed the proof.','A fresh worker has no trusted status registry.')
    if(!completeWorkProfile.enabled)refuse('counted-profile-required','Start the worker with GDP_WORK_FULL=1 before importing the engine.','The complete counted-work profile is not enabled.')
    const q=request, ls=q.laws!
    const proof=(u:Unit,l:Law)=>proofSummary(invoke(()=>proveLaws(u.rule,[l])))
    const witness=(m:Machine,l:Law)=>{const found=invoke(()=>search(m,l,q.budget.depth,q.budget.bound));if(!found)return null;const run=interpret(m);let state=run.init(found.params);
      const initial={...state.scalars},steps=found.trace.map(input=>{state=run.step(found.params,state,input);return {input,after:{...state.scalars}}});return {params:found.params,initial,steps,explanation:`${l.name} fails from ${JSON.stringify(initial)} under parameters ${JSON.stringify(found.params)}${steps.length?': '+steps.map((s,i)=>`step ${i+1}, input ${JSON.stringify(s.input)} -> ${JSON.stringify(s.after)}`).join('; '):' in the initial state'}. Shortest within the reported finite domain, not globally minimal.`,minimality:{kind:'shortest-in-existing-finite-search',maxDepth:q.budget.depth,defaultValueBound:q.budget.bound,note:'Existing search also honors explicit scalar upper bounds up to15; this is not a global unbounded minimality claim.'}}}
    const output=withBudget(q.budget.work,()=>workLedger.withCapacityRefusalBoundary(()=>{
      if(q.tool==='prove'){
        const u=q.subject!,verdicts=ls.map(l=>({law:l.name,...proof(u,l)})),proven=verdicts.every(v=>v.proven&&v.checked)
        return {subject:binding(u,ls),label:proven?'proven':'not adequate',result:{verdicts},statusEvidence:[{...binding(u,ls),proven,checked:proven,laws:ls.map(l=>l.name)}],explanation:`${u.unit}: ${proven?'every requested law has a checked inductive proof':'not every requested law has a checked proof'}. Checked state names: ${Object.keys(u.rule.state).join(', ')}; parameters: ${u.rule.params.join(', ')||'none'}. This is a rule proof, not native conformance.`}
      }
      if(q.tool==='why_not'){
        const u=q.subject!,cases=ls.map(l=>({law:l.name,counterexample:witness(u.rule,l)}))
        return {subject:binding(u,ls),result:{cases},explanation:`${u.unit}: ${cases.filter(c=>c.counterexample).length} requested law(s) have a reachable interpreter counterexample in the stated finite domain. Traces use the original parameter, input and state names; absence of a trace does not prove a law.`}
      }
      if(q.tool==='suggest'){
        const u=q.subject!,known=ls.map(l=>({law:l.name,...proof(u,l),source:source(l)}))
        const inferred=invoke(()=>inferLaws(u.rule,ls,[],{runs:128,maxCandidates:q.budget.candidates,timed:false,minimize:false,ms:q.budget.work/250,wall:Infinity}))
        const found=inferred.found.slice(0,8), support=[...ls,...found.map(f=>f.law)]
        const closure=found.length?proofSummary(invoke(()=>proveLaws(u.rule,support))):null
        const discovered=found.map(f=>({law:f.law.name,...closure,source:source(f.law),builderSource:f.source??null,support: support.map(l=>l.name),supportSource:`import type {Law} from 'gdp-wired/machine'\nconst support: Law[] = ${JSON.stringify(support)}\n`}))
        const nearMisses=(q.nearMisses??[]).map(l=>({law:l.name,source:source(l),counterexample:witness(u.rule,l)}))
        return {subject:binding(u,ls),result:{satisfied:known.filter(p=>p.proven&&p.checked),discovered:discovered.filter(p=>p.proven&&p.checked),nearMisses:nearMisses.filter(n=>n.counterexample),unresolvedNearMisses:nearMisses.filter(n=>!n.counterexample).map(n=>n.law),inference:{proven:inferred.proven===true,checked:inferred.checked===true,samples:inferred.stats.samples,candidates:inferred.stats.candidates,stopped:inferred.stats.stopped},nearMissSource:'caller-supplied candidate laws; no new candidate synthesis engine'},explanation:`${u.unit}: existing inferLaws generated candidate laws; only checked laws or jointly checked support sets are returned as satisfied/discovered. Supplied near misses are returned only with a real bounded counterexample. Each item includes pasteable source; no statistical sample is promoted to a proof.`}
      }
      if(q.tool==='check_change'){
        const a=q.before!,b=q.after!
        const rows=ls.map(l=>{const before=proof(a,l),after=proof(b,l);return {law:l.name,before,after,counterexample:before.proven&&before.checked&&!(after.proven&&after.checked)?witness(b.rule,l):null}})
        const composed=refinement(b.rule,a.rule,{relation:agree(a.rule),witness:Object.fromEntries(a.rule.inputs.map(n=>[n,{op:'var' as const,name:n}]))})
        const relation=proofSummary(invoke(()=>proveLaws(composed.machine,composed.laws)))
        const allowed=proofSummary(invoke(()=>proveStepLaws(composed.machine,composed.laws,composed.stepLaws)))
        let difference:unknown=null
        if(!(relation.proven&&relation.checked&&allowed.proven&&allowed.checked))for(const l of composed.laws){difference=witness(composed.machine,l);if(difference)break}
        const refines=relation.proven&&relation.checked&&allowed.proven&&allowed.checked
        return {subject:binding(b,ls),before:binding(a,ls),result:{stillHold:rows.filter(r=>r.after.proven&&r.after.checked).map(r=>r.law),newlyBroken:rows.filter(r=>r.counterexample).map(r=>({law:r.law,trace:r.counterexample})),lostProof:rows.filter(r=>r.before.proven&&r.before.checked&&!(r.after.proven&&r.after.checked)&&!r.counterexample).map(r=>r.law),verdicts:rows,behaviour:{scope:'after refines before under the implementation precondition; identity input witness, equality state relation; not bidirectional equivalence',status:refines?'checked-refinement':difference?'bounded-difference':'unresolved',relation,allowed,trace:difference,stateNames:{a:'after',b:'before'}}},statusEvidence:[{...binding(a,ls),proven:rows.every(r=>r.before.proven&&r.before.checked),checked:rows.every(r=>r.before.proven&&r.before.checked),laws:ls.map(l=>l.name)},{...binding(b,ls),proven:rows.every(r=>r.after.proven&&r.after.checked),checked:rows.every(r=>r.after.proven&&r.after.checked),laws:ls.map(l=>l.name)}],explanation:`${b.unit}: ${rows.filter(r=>r.counterexample).length} previously checked law(s) now have a real counterexample; ${rows.filter(r=>r.after.proven&&r.after.checked).length} remain checked. Behaviour uses the existing compose.refinement machine and both invariant and request-admissibility checks; an unknown proof is not itself a behaviour difference.`}
      }
      return refuse('unknown-tool','Use a documented tool.','No implementation for this tool')
    }))
    const assumptions=context(q)
    if('statusEvidence' in output)for(const record of output.statusEvidence??[])Object.assign(record,{assumptions})
    const after=workLedger.snapshot()
    return {schema:'gdp-wired/agent-tool/v1',tool:q.tool,ok:true,...output,assumptions,budget:{limits:q.budget,apiCalls:calls,work:exactRaw(workSub(workFromExact(after.actual),workFromExact(before.actual))),counters:counterDelta(before,after),profile:completeWorkProfile.id,provisional:true}}
  }catch(e){const after=workLedger.snapshot();return {...failure(String(tool),e),assumptions:request?context(request):null,budget:{limits:request?.budget??null,apiCalls:calls,work:exactRaw(workSub(workFromExact(after.actual),workFromExact(before.actual))),counters:counterDelta(before,after),profile:completeWorkProfile.id,provisional:true}}}
}
