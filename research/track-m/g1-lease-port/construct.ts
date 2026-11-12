// Research-only paired regression: reconstruct the frozen half through the exact
// lease API, then let a fresh process independently check all 19 laws/38 goals.
// The diagnostic grant below is NOT a calibrated production bar or b_min.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {protocols} from '../../protocols/ic3syn/models.ts'
import {countsDump,guardLaws,certFor} from '../../../core/counts.ts'
import {proveRule} from '../../../core/dsl.ts'
import {type Law,type Machine} from '../../../core/machine.ts'
import {discoverLiftedCountGuard} from '../../../core/count-lifted-shape.ts'
import {discoverLiftedCountPrerequisites} from '../../../core/count-lifted-prerequisite.ts'
import {proveLiftedCountComposition} from '../../../core/count-lifted-strategy.ts'
import {liftedWorkLeaseBudget,type LiftedWorkSlice} from '../../../core/count-lifted-budget.ts'
import {workAmount,workFromExact,compareWork,workShare} from '../../../core/work-amount.ts'
import {workAdmissionSnapshot,workLedger} from '../../../core/work-admission.ts'
import {completeWorkProfile} from '../../../core/work-profile.ts'
import {bindClosedFamily,substituteClosedFamily,type ClosedFamily} from './closed-family.ts'
const file=process.argv[2],out=process.argv[3]
if(!file||!out||!completeWorkProfile.enabled)throw Error('expected fixture, output directory and FULL accounting')
mkdirSync(out,{recursive:true})
const expected='95321d6ef8303cdef66dbb376e1ba9639cbf9c8b2f7768324570ab2133968a8e',input=readFileSync(file,'utf8').trim()
if(createHash('sha256').update(input).digest('hex')!==expected)throw Error('input family hash mismatch')
const closed=JSON.parse(input) as ClosedFamily,original=workAmount(3_000_000_000n),slices:LiftedWorkSlice[]=[],events:Record<string,unknown>[]=[]
const report:Record<string,unknown>={format:'g1-replay-lease-pair-v1',qualification:false,expectedFamily:expected,original:{numerator:String(original.num),denominator:String(original.den)},flags:Object.fromEntries(Object.entries(process.env).filter(([k])=>k.startsWith('GDP_')).sort(([a],[b])=>a.localeCompare(b))),passed:false}
const budget=liftedWorkLeaseBudget(original,{observe:slice=>slices.push(slice)})
try{workLedger.withBudget(original,()=>{
 const epoch=workAdmissionSnapshot().rootEpoch;let admission:{machine:Machine,laws:Law[]}|undefined
 // Preserve the historical admission recipe and its order; only its candidate
 // event is consumed, never a proof, exclusion, cache entry or saved verdict.
 for(const protocol of protocols){
  const rule=protocol.make(),seed=guardLaws(rule.machine),extended={...rule.machine,counts:{...rule.machine.counts,...seed.counts}}
  if(!seed.laws.some(law=>discoverLiftedCountGuard(extended,law,seed.laws)))continue
  const prior=countsDump.on,stop={}
  countsDump.on=(event:object)=>{const candidate=event as {phase?:string,machine:Machine,laws:Law[]};if(candidate.phase==='candidates'){admission={machine:candidate.machine,laws:candidate.laws};throw stop}}
  try{proveRule(rule,protocol.laws(rule),{search:{ms:4_000_000}})}catch(error){if(error!==stop)throw error}finally{countsDump.on=prior}
  if(admission)break
 }
 if(!admission)throw Error('missing original generator admission')
 const family=bindClosedFamily(admission.machine,admission.laws,closed),law=family.find(law=>discoverLiftedCountPrerequisites(closed.machine,law,family).length)
 if(!law||family.length!==19)throw Error('missing half target or wrong closed family')
 report.target=family.indexOf(law);report.before=workAdmissionSnapshot()
 const proof=proveLiftedCountComposition(closed.machine,family,law,Infinity,(goal,decls)=>certFor(goal,decls,false,0,()=>true),event=>events.push(event),budget)
 report.after=workAdmissionSnapshot()
 if(!proof||proof.status)throw Error('composition did not return an independently checked proof')
 if(workAdmissionSnapshot().rootEpoch!==epoch||workAdmissionSnapshot().activeEndpoints.length!==1)throw Error('root changed or child scope leaked')
 if(!slices.some(s=>s.kind==='case')||!slices.some(s=>s.kind==='leaf')||new Set(slices.map(s=>s.scopeId)).size!==slices.length)throw Error('missing or reused exact slice identity')
 for(const slice of slices)if(slice.rootEpoch!==epoch||compareWork(slice.allocation,workShare(original,1n,slice.kind==='case'?30n:120n))!==0)throw Error('wrong root or slice allocation')
 const current=workAdmissionSnapshot();if(compareWork(workFromExact(current.actual),workFromExact(current.activeEndpoints[0]!.end))>0)throw Error('root exceeded')
 const completed=substituteClosedFamily(closed,law,proof),text=JSON.stringify(completed),sha=createHash('sha256').update(text).digest('hex')
 writeFileSync(out+'/family.json',text+'\n');report.familySha256=sha;report.same95321=sha===expected
 if(sha!==expected)throw Error('reconstructed family differs from the frozen 95321 family')
 report.passed=true
})}catch(error){report.error={name:error instanceof Error?error.name:'unknown',message:error instanceof Error?error.message:String(error),refusal:workLedger.capacityRefusal(error)};process.exitCode=1}
finally{report.settled=workAdmissionSnapshot();report.events=events;report.slices=slices.map(s=>({...s,allocation:{numerator:String(s.allocation.num),denominator:String(s.allocation.den)}}));writeFileSync(out+'/construction.json',JSON.stringify(report,null,2)+'\n')}
