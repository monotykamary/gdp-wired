import {strict as a} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const [root,id]=process.argv.slice(2),path=join(root!,'core/exists.ts'),source=readFileSync(path,'utf8')
const hash=(text:string)=>createHash('sha256').update(text).digest('hex')
const skip="if (cls !== undefined && covered!.has(cls)) continue"
const keep="if (cls !== undefined) covered!.add(cls)"
a.equal(source.split(skip).length,2);a.equal(source.split(keep).length,2)
// Audit-only adapter in the disposable extracted source. Never written into the
// integration worktree. Oracle calls do not increment smallWithin's steps.
const instrumented=source.replace(skip,"if (cls !== undefined && covered!.has(cls)) { (globalThis as any).__quotientAudit.skip(m, p, st, r, cls, run.step); continue }")
 .replace(keep,"if (cls !== undefined) { covered!.add(cls); (globalThis as any).__quotientAudit.keep(m, st, cls, next) }")
writeFileSync(path,instrumented)
const canonical=(m:any,s:any)=>JSON.stringify({
 scalars:Object.entries(s.scalars).sort(([a],[b])=>a.localeCompare(b)),
 maps:Object.entries(s.maps).sort(([a],[b])=>a.localeCompare(b)).map(([name,cells]:any)=>{
  const d=s.defaults?.[name]??m.maps?.[name]??0
  return[name,d,[...cells].filter(([,v]:any)=>v!==d).sort((a:any,b:any)=>a[0]-b[0])]
 }),
})
const representatives=new WeakMap<object,Map<number,string>>()
let skipped=0,matched=0,refused=0,kept=0
;(globalThis as any).__quotientAudit={
 keep(m:any,st:object,cls:number,next:any){let map=representatives.get(st);if(!map){map=new Map();representatives.set(st,map)}a(!map.has(cls));map.set(cls,canonical(m,next));kept++},
 skip(m:any,p:any,st:object,r:any,cls:number,step:any){
  skipped++;const expected=representatives.get(st)?.get(cls);a.notEqual(expected,undefined)
  let next:any
  try{next=step(p,st,r)}catch(error){if((error as Error).name==='BudgetExpired')throw error;refused++;return}
  a.equal(canonical(m,next),expected,`distinct skipped successor in ${id}, class ${cls}`);matched++
 },
}
const {protocols}=await import(join(root!,'research/protocols/ic3syn/models.ts'))
const {small}=await import(join(root!,'core/exists.ts'))
const protocol=protocols.find((p:any)=>p.id===id);a(protocol,'missing original '+id)
const m=protocol.make().machine,parameters=m.params.length?[2,3]:[2],rows:any[]=[]
for(const value of parameters){
 const p=Object.fromEntries(m.params.map((name:string)=>[name,value]))
 process.env.GDP_REQUEST_QUOTIENT='0';const before=small(m,p,3,3000,300000,100000).map((s:any)=>canonical(m,s))
 const initial={skipped,matched,refused,kept}
 process.env.GDP_REQUEST_QUOTIENT='1';const after=small(m,p,3,3000,300000,100000).map((s:any)=>canonical(m,s))
 a.deepEqual(after,before,'sample changed for '+id)
 rows.push({params:p,states:before.length,digest:hash(JSON.stringify(before)),skipped:skipped-initial.skipped,matched:matched-initial.matched,refused:refused-initial.refused,kept:kept-initial.kept})
}
a.equal(skipped,matched+refused)
console.log('QUOTIENT_SKIPPED_AUDIT '+JSON.stringify({id,source:process.env.QUOTIENT_SOURCE,originalSamplerSHA256:hash(source),instrumentedSamplerSHA256:hash(instrumented),adapterEdits:2,skipped,matched,refused,kept,rows,workMode:'logical trial budget only; no counted endpoint during oracle re-execution'}))
