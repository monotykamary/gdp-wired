// One original-budget run. The optional meter is installed only in a disposable snapshot.
import {readFileSync} from 'node:fs'
import {PerformanceObserver} from 'node:perf_hooks'
import {costMeter,costSpan,type CostPhase} from './cost-meter.ts'
import {rowMeter} from './row-meter.ts'
import {generatorStats} from './generator-meter.ts'
import {rowReuseStats} from '../../kernel/prover-rows.ts'
import {certFor,candidates,guardLaws} from '../../core/counts.ts'
import {proveFocusedCounts} from '../../core/count-focus-proof.ts'
import {countedObligations,checkMC} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
import {smallOf,trueSmall} from '../../core/exists.ts'
const [mode='focused',input,prefix='Inv1758']=process.argv.slice(2)
const start=performance.now(),cpu=process.cpuUsage(),work=fullWork(),trace:Record<string,unknown>[]=[]
let outcome:Record<string,unknown>,gcMs=0,gcEvents=0
const gcSupported=PerformanceObserver.supportedEntryTypes.includes('gc')
const observer=gcSupported?new PerformanceObserver(list=>{for(const e of list.getEntries()){gcMs+=e.duration;gcEvents++}}):undefined
observer?.observe({entryTypes:['gc']})
if(mode==='focused'){
 const {m,laws}=costSpan('construction','fixture-load',()=>JSON.parse(readFileSync(input!,'utf8'))),index=laws.findIndex((l:any)=>l.name.startsWith(prefix)),law=laws[index]
 if(!law)throw new Error(`law not found: ${prefix}`)
 const result=withWall(start+60000,()=>counted(fullRate,()=>costSpan('construction','focused-control',()=>{
  const proof=proveFocusedCounts(m,laws,law,{},clock()+5000,(goal,decls)=>certFor(goal,decls,true,1000),event=>trace.push(event))
  return {proven:!!proof,checked:!!proof&&countedObligations(m,laws,{[law.name]:proof.instances},index).every(p=>!!proof.certs[p.goal.name]&&checkMC(p.goal.hyps,p.decls,proof.certs[p.goal.name]!))}
 }),true))
 outcome={law:law.name,...result}
}else if(mode==='generation'||mode==='production'){
 const {protocols}=await import('../protocols/ic3syn/models.ts')
 const {proveRule}=await import('../../core/dsl.ts')
 const protocol=protocols.find(p=>p.id==='mldr')!
 if(mode==='generation'){
  outcome=withWall(start+60000,()=>costSpan('generation','original-mlDR-generation',()=>{
   const r=protocol.make(),m0=r.machine,caller=protocol.laws(r),g=guardLaws(m0),m={...m0,counts:{...m0.counts,...g.counts}}
   smallOf(m)
   return counted(fullRate,()=>{
    const valid=caller.every(l=>trueSmall(m,[l])),set=valid?candidates(m0,m,caller,caller,g.laws,60000,clock()+60000):[]
    return {machine:m.name,callerCount:caller.length,candidateCount:set.length,candidates:set.map(l=>l.name),smallStateValid:valid}
   },true)
  },true))
 }else{
  const r=protocol.make(),laws=protocol.laws(r)
  const result=withWall(start+60000,()=>costSpan('construction','original-harness-control',()=>proveRule(r,laws,{search:{ms:60000}})))
  outcome={machine:r.machine.name,proven:result.proven,checked:result.checked,...('why'in result?{why:String(result.why)}:{}),...('goal'in result?{goal:result.goal}:{}),callerCount:laws.length}
 }
}else throw new Error(`unknown mode: ${mode}`)
const wallMs=performance.now()-start,spent=process.cpuUsage(cpu),countedMs=(fullWork()-work)/fullRate
await new Promise<void>(resolve=>setImmediate(resolve));observer?.disconnect()
const snapshot=costMeter.snapshot(),phases=Object.fromEntries((['generation','search','construction','kernel'] as CostPhase[]).map(k=>[k,snapshot.phases[k]?.exclusiveMs??0])),accounted=Object.values(phases).reduce((a,b)=>a+b,0)
const affinity=process.platform==='linux'?readFileSync('/proc/self/status','utf8').match(/^Cpus_allowed_list:\s*(.+)$/m)?.[1]?.trim():undefined
console.log(JSON.stringify({mode,affinity,rowReuse:rowReuseStats,generators:generatorStats,finalProofGeneratorUsage:null,rows:rowMeter.snapshot(),profiled:costMeter.enabled,...outcome,wallMs,countedMs,cpuMs:{user:spent.user/1000,system:spent.system/1000},phases,idleGcResidualMs:wallMs-accounted,gcObservation:{supported:gcSupported,events:gcEvents,observedMs:gcMs,policy:'GC within a timed scope stays charged to that scope; residual is not a GC-only estimate'},sites:Object.entries(snapshot.sites).sort((a,b)=>b[1].exclusiveMs-a[1].exclusiveMs).slice(0,24),traceEvents:trace.length,tail:trace.slice(-4)}))
