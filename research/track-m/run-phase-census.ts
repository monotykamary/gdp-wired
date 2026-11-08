// Same-input wall census. This is not a proof strategy or acceptance gate.
import {readFileSync} from 'node:fs'
import {type Law,type Machine} from '../../core/machine.ts'
import {certFor,countedAttempts} from '../../core/counts.ts'
import {type CountCert,type Instances,check,checkMC,countedObligations} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,usedHyps,withTrees,withWall} from '../../kernel/prove.ts'
import {census,type PhaseCensus} from './phase-census-meter.ts'

const [mode='focused',input,side='candidate']=process.argv.slice(2)
if(!['focused','native'].includes(mode)||!input)throw new Error('focused|native INPUT SIDE required')
const {m,laws}=JSON.parse(readFileSync(input,'utf8')) as {m:Machine,laws:Law[]}
const prefixes=mode==='focused'?['one primary','Inv3915','Inv1758','Inv2973','Inv*']:['one primary','Inv3915','Inv1758']
const focused=mode==='focused'?(await import('../../core/count-focus-proof.ts')).proveFocusedCounts:undefined
const profiled=process.env.TRACK_M_PHASE_CENSUS==='1'
const detail=process.env.LAB_SECTION7_T1==='1'?(await import('./section7-cost-meter.ts')).detail:undefined
const results:{record:any,audit:PhaseCensus}[]=[]
withTrees(()=>{
 for(const prefix of prefixes){
  const law=laws.find(l=>l.name.startsWith(prefix));if(!law)throw new Error('missing '+prefix)
  const index=laws.indexOf(law),trace:Record<string,unknown>[]=[]
  census.enabled=profiled;census.reset();detail?.reset(law.name)
  const start=performance.now(),before=fullWork()
  const verdict=census.run('other','law total',()=>withWall(start+60000,()=>counted(fullRate,()=>{
   const until=clock()+5000
   let proof:{instances:Instances,certs:Record<string,CountCert>}|undefined
   if(focused)proof=focused(m,laws,law,{},until,(g,ds)=>certFor(g,ds,true,1000),event=>trace.push(event))
   else {const result=countedAttempts(m,[law],new Set<Law>(),until).traced(law,laws,1,5000);if('proof'in result)proof=result.proof}
   const checked=!!proof&&countedObligations(m,laws,{[law.name]:proof.instances},index).every(p=>!!proof.certs[p.goal.name]&&checkMC(p.goal.hyps,p.decls,proof.certs[p.goal.name]!))
   return {proven:!!proof,checked}
  },true)))
  const wallMs=performance.now()-start,countedUnits=(fullWork()-before)/fullRate,snapshot=census.snapshot()
  // Do not check or traverse proof dependencies between laws: that would warm
  // row caches before the next law and invalidate the shared-cache control.
  results.push({audit:census.capture(),record:{mode:'phase-census',side,entry:mode,profiled,law:law.name,warmup:mode==='native'&&prefix!=='Inv1758',...verdict,wallMs,countedUnits,phases:snapshot.exclusiveMs,accountedMs:Object.values(snapshot.exclusiveMs).reduce((a,b)=>a+b,0),sites:snapshot.sites,traceEvents:trace.length,...(detail?{t1:detail.capture()}:{})}})
 }
})
census.enabled=false
if(process.env.LAB_SECTION7_FOLLOWUP==='1'){const {followup}=await import('./section7-followup-meter.ts');for(const audit of followup.audits())console.log(JSON.stringify(audit))}
let auditWallMs=0
for(const {record,audit:captured} of results){
 const audit=captured.audit(check,usedHyps);auditWallMs+=audit.wallMs
 console.log(JSON.stringify({...record,closureCount:audit.closures.length,cutCounts:audit.counts,cutIds:audit.ids,closures:audit.closures,leaves:audit.leaves,auditWallMs:audit.wallMs,proofAudit:audit.raw}))
}
console.log(JSON.stringify({mode:'phase-census-total',side,entry:mode,profiled,laws:results.length,wallMs:results.reduce((sum,r)=>sum+r.record.wallMs,0),auditWallMs}))
