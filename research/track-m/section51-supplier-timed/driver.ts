// External diagnostic adapter. No production module or function is replaced.
import {readFileSync,realpathSync} from 'node:fs'
import {join} from 'node:path'
import {pathToFileURL} from 'node:url'
import {hash,save,encode} from './io.ts'
import {phaseMarker} from './phase-marker.ts'
import {requireRootRaw} from './root-policy.ts'
import {replayDiagnosticCollector,REPLAY_DIAGNOSTIC_LIMITS} from './replay-diagnostic.ts'
import {countReplayDiagnostic} from '../../../core/count-replay-diagnostic.ts'
const [input,out,mode]=process.argv.slice(2)
if(!input||!out||!['timed','instrumented'].includes(mode!))throw Error('invalid driver arguments')
const marker=phaseMarker(join(out,'phase-marker.tsv'))
let phase='imports'
const setPhase=(value:string)=>{phase=value;marker.mark(value)}
marker.mark('configuration')
const config=JSON.parse(readFileSync(join(input,'CONFIG.json'),'utf8'))
const rootRaw=requireRootRaw(config),rootUnits=BigInt(rootRaw)
const flags=JSON.parse(readFileSync(join(input,'active-flags.json'),'utf8'))
for(const [key,value]of Object.entries(flags))if(process.env[key]!==value)throw Error('flag mismatch '+key)
if(Object.keys(process.env).filter(k=>k.startsWith('GDP_')).sort().join()!==Object.keys(flags).sort().join())throw Error('unexpected GDP configuration')
if(hash(readFileSync(process.execPath))!==config.runtime.bun.sha256||Bun.version!==config.runtime.bun.version)throw Error('wrong native Bun')
marker.mark('imports')
const [{protocols},{proveRule},native,{workLedger},{countsDump},{workKeys},{workAmount}]=await Promise.all([
 import('../../protocols/ic3syn/models.ts'),import('../../../core/dsl.ts'),import('../../../kernel/prove.ts'),
 import('../../../core/work-admission.ts'),import('../../../core/counts.ts'),import('../../../core/work-kinds.ts'),import('../../../core/work-amount.ts')])
const target=process.env.MLDR_TARGET;if(!target)throw Error('missing target binding')
const direct=await import(pathToFileURL(join(target,'core/work-admission.ts')).href)
if(direct.workLedger!==workLedger)throw Error('driver and target do not share the native ledger')
const rootWork=workAmount(rootUnits)
const p=protocols.find(x=>x.id==='mldr');if(!p)throw Error('missing original MLDR protocol')
if(countsDump.on!==undefined)throw Error('unexpected preinstalled counts observer')
const expectedWeights=JSON.parse(readFileSync(join(input,'weights.json'),'utf8'))
const initialWeights=workLedger.snapshot().weights
if(JSON.stringify(initialWeights)!==JSON.stringify(expectedWeights))throw Error('native frozen weights differ')
const identity={serialization:'mldr-3g-data/v2',sourceCommit:config.source.commit,sourceTree:config.source.tree,profileSHA256:config.profileSHA256,mode,runtime:{version:Bun.version,sha256:hash(readFileSync(process.execPath)),path:realpathSync(process.execPath)},protocol:p.id,rootRaw}
save(join(out,'identity.json'),identity)
if(countReplayDiagnostic.on!==undefined)throw Error('unexpected replay diagnostic observer')
const replayDiagnostics=replayDiagnosticCollector({...identity,sealSHA256:hash(readFileSync(join(input,'SEAL.json'))),inputIndexSHA256:hash(readFileSync(join(input,'INPUTS.sha256')))})
countReplayDiagnostic.on=replayDiagnostics.capture
const {installClosingCapture}=await import(pathToFileURL(join(target,'research/track-m/section51-closing-feedback/capture.ts')).href)
const removeClosingCapture=installClosingCapture(out,identity,setPhase)
let initial:any,final:any,settled:any,value:any,error:any,model:any,laws:any,trace:any,observer:any
marker.mark('ready')
const observerFactory=mode==='instrumented'?(await import('./observer.ts')).observer:undefined
const start=process.hrtime.bigint()
try{
 native.withBudget(rootWork,()=>{
  initial=workLedger.snapshot()
  const go=()=>{
   try{
    setPhase('make');const r=p.make();setPhase('laws');const ls=p.laws(r)
    observer?.beginMeasurement(ls.map(l=>l.name))
    // Same read-only custody snapshot in both arms, before public proving.
    marker.mark('custody-clone');model=structuredClone(r.machine);laws=structuredClone(ls)
    setPhase('prove');value=proveRule(r,ls,{search:{work:rootWork}});setPhase('returned')
   }catch(e){error={name:e instanceof Error?e.name:'unknown',message:String(e),phase,capacity:workLedger.capacityRefusal(e)??null};setPhase('threw')}
  }
  if(observerFactory){
   observer=observerFactory(out,initial,config.trace,identity)
   countsDump.on=event=>observer.count(event,workLedger.snapshot())
   try{workLedger.withTrace(event=>observer.event(event),go)}finally{countsDump.on=undefined;final=workLedger.snapshot();trace=observer.finish(final)}
  }else{try{go()}finally{final=workLedger.snapshot()}}
 })
}catch(e){error??={name:e instanceof Error?e.name:'unknown',message:String(e),phase,capacity:workLedger.capacityRefusal(e)??null}}
const closingSnapshots=removeClosingCapture()
marker.mark('settling')
settled=workLedger.snapshot()
countReplayDiagnostic.on=undefined
marker.mark('diagnostic-finalize')
save(join(out,'replay-declines.json'),replayDiagnostics.finish(countReplayDiagnostic.observerFailures),REPLAY_DIAGNOSTIC_LIMITS.aggregateBytes)
const end=process.hrtime.bigint()
if(!initial||!final)throw Error('missing in-root snapshot; diagnostic incomplete')
const deltas=Object.fromEntries(workKeys.map(k=>[k,String(BigInt(final.counters[k])-BigInt(initial.rootBaseline.counters[k]))]))
const q=(x:any)=>({n:BigInt(x.numerator),d:BigInt(x.denominator)})
const a=q(final.actual),r=q(final.reserved),base=q(initial.rootBaseline.actual)
const root=final.activeEndpoints.find((x:any)=>x.kind==='root'),e=root&&q(root.end)
const bounded=!!e&&(a.n*r.d+r.n*a.d)*e.d<=e.n*a.d*r.d&&(e.n*base.d-base.n*e.d)===rootUnits*e.d*base.d
const clean=settled.activeEndpoints.length===0&&settled.rootBaseline===null&&settled.effectiveEnd===null&&q(settled.reserved).n===0n
const normal=!error||error.name==='BudgetExpired'
const result={schema:'mldr-3g-diagnostic/v2',identity,mode,closingSnapshots,originalRootRaw:rootRaw,rawVerdict:value??null,error:error??null,phase,verdict:value?.proven&&value?.checked?'proven':value?.run?'refuted':'unknown',initial,final,settled,counterDeltas:deltas,wallNs:String(end-start),bounded,settledClean:clean,zeroFinalReserved:q(final.reserved).n===0n,trace:trace??null,observerInstalled:mode==='instrumented',qualification:false,WClaim:false,diagnosticComplete:value!==undefined&&normal&&bounded&&clean&&q(final.reserved).n===0n&&(mode==='timed'||trace?.complete===true)}
marker.mark('save-artifacts')
if(model){save(join(out,'original-model.json'),model);save(join(out,'original-laws.json'),laws);(result as any).modelSHA256=hash(encode(model,64*1024*1024));(result as any).lawsSHA256=hash(encode(laws,64*1024*1024))}
const totalCountedUnits={numerator:String(a.n*base.d-base.n*a.d),denominator:String(a.d*base.d)}
const measurement={schema:'mldr-measurement-total/v1',authority:'MEASUREMENT_ONLY',mode,rootCeilingRaw:rootRaw,totalCountedUnits,counterDeltas:deltas,observedWallNs:result.wallNs,wallMeaning:'OBSERVATION_ONLY',publicProvenAndChecked:value?.proven===true&&value?.checked===true,phase,error:error??null,referenceConversion:{status:'PENDING_RHO_NEW',rhoNew:null,seconds:null},qualification:false,WClaim:false,verdictAuthority:false}
if(observer)try{save(join(out,'measurement-rows.json'),observer.measurement(result))}catch(e){save(join(out,'measurement-error.json'),{error:String(e)});result.diagnosticComplete=false}
save(join(out,'measurement-total.json'),measurement)
save(join(out,'verdict.json'),result);save(join(out,'root-initial.json'),initial);save(join(out,'root-final-before-unwind.json'),final);save(join(out,'root-settled.json'),settled)
marker.mark('complete')
const phaseStatusExported=marker.saveStatus(status=>save(join(out,'phase-marker-status.json'),{...status,scope:'coarse driver phases; proof subphase not inferred'}))
console.log(JSON.stringify({mode,verdict:result.verdict,diagnosticComplete:result.diagnosticComplete,wallNs:result.wallNs,traceComplete:trace?.complete??null,phaseStatusExported,phaseStatusExportFailures:marker.statusExportFailures,qualification:false}))
if(!result.diagnosticComplete)process.exitCode=86
