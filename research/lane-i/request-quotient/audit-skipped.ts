import {strict as a} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {SkippedRequestOracle,exceptionDifference} from './skipped-oracle.ts'
const [root,id]=process.argv.slice(2),path=join(root!,'core/exists.ts'),source=readFileSync(path,'utf8')
const hash=(text:string)=>createHash('sha256').update(text).digest('hex')
const skip='if (cls !== undefined && covered!.has(cls)) continue',keep='if (cls !== undefined) covered!.add(cls)'
a.equal(source.split(skip).length,2);a.equal(source.split(keep).length,2)
const instrumented=source.replace(skip,'if (cls !== undefined && covered!.has(cls)) { (globalThis as any).__quotientAudit.skip(m, p, st, r, cls, run.step); continue }')
 .replace(keep,'if (cls !== undefined) { covered!.add(cls); (globalThis as any).__quotientAudit.keep(m, st, cls, next) }')
const machinePath=join(root!,'core/machine.ts'),machineSource=readFileSync(machinePath,'utf8')
const guard='if (m.assume && !evalC(m.assume, env, st, plain)) throw new RangeError(refused(m))'
const interpreterSHA256='03d69e7e9e768a7e6735294f819da90d965f73d72c4134ab9ef74715d36f51bf'
a.equal(hash(machineSource),interpreterSHA256);a.equal(machineSource.split(guard).length,2)
const guardLine=machineSource.slice(0,machineSource.indexOf(guard)).split('\n').length;a.equal(guardLine,819)
const instrumentedMachine=machineSource.replace(guard,'if (m.assume && !evalC(m.assume, env, st, plain)) throw (globalThis as any).__quotientAudit.assumptionFailure(new RangeError(refused(m)), m)')
// Exactly two sampler hooks and one origin-branding hook, in disposable source
// only. The latter brands the original RangeError at the unchanged guard branch.
writeFileSync(path,instrumented);writeFileSync(machinePath,instrumentedMachine)
const canonical=(m:any,s:any)=>JSON.stringify({
 scalars:Object.entries(s.scalars).sort(([a],[b])=>a.localeCompare(b)),
 maps:Object.entries(s.maps).sort(([a],[b])=>a.localeCompare(b)).map(([name,cells]:any)=>{
  const d=s.defaults?.[name]??m.maps?.[name]??0
  return[name,d,[...cells].filter(([,v]:any)=>v!==d).sort((a:any,b:any)=>a[0]-b[0])]
 }),
})
const oracle=new SkippedRequestOracle({file:'core/machine.ts',sha256:interpreterSHA256,line:guardLine,expression:guard},canonical)
;(globalThis as any).__quotientAudit=oracle
const {protocols}=await import(join(root!,'research/protocols/ic3syn/models.ts'))
const {small}=await import(join(root!,'core/exists.ts'))
const protocol=protocols.find((p:any)=>p.id===id);a(protocol,'missing original '+id)
const m=protocol.make().machine,parameters=m.params.length?[2,3]:[2],rows:any[]=[]
try{
 for(const value of parameters){
  const p=Object.fromEntries(m.params.map((name:string)=>[name,value]))
  process.env.GDP_REQUEST_QUOTIENT='0';const before=small(m,p,3,3000,300000,100000).map((s:any)=>canonical(m,s))
  const initial=oracle.snapshot()
  process.env.GDP_REQUEST_QUOTIENT='1';const after=small(m,p,3,3000,300000,100000).map((s:any)=>canonical(m,s))
  a.deepEqual(after,before,'sample changed for '+id)
  const now=oracle.snapshot()
  rows.push({params:p,states:before.length,digest:hash(JSON.stringify(before)),skipped:now.skipped-initial.skipped,matched:now.matched-initial.matched,refused:now.refused-initial.refused,kept:now.kept-initial.kept,unexpected:now.unexpected-initial.unexpected,exceptionHistogram:exceptionDifference(initial,now)})
 }
}catch(error){console.log('QUOTIENT_SKIPPED_AUDIT_FAILURE '+JSON.stringify({id,source:process.env.QUOTIENT_SOURCE,...oracle.snapshot(),rows}));throw error}
const {exceptions:exceptionHistogram,...summary}=oracle.snapshot();a.equal(summary.unexpected,0);a.equal(summary.skipped,summary.matched+summary.refused)
console.log('QUOTIENT_SKIPPED_AUDIT '+JSON.stringify({id,source:process.env.QUOTIENT_SOURCE,originalSamplerSHA256:hash(source),instrumentedSamplerSHA256:hash(instrumented),originalInterpreterSHA256:interpreterSHA256,instrumentedInterpreterSHA256:hash(instrumentedMachine),adapterEdits:2,interpreterAdapterEdits:1,...summary,exceptionHistogram,rows,workMode:'logical trial budget only; no counted endpoint during oracle re-execution'}))
