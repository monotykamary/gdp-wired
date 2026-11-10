// Section 10: extend the exact captured packet by one ordinary count instance.
import {readFileSync} from 'node:fs'
import {type C,less,same,x} from '../../core/machine.ts'
import {type CountDecl,type CountInst,type Goal,type LemmaCut,type Path,canon,columnTerm,linear,truth} from '../../kernel/kernel.ts'
import {brokenOf,clock,counted,fullRate,fullWork,usedHyps,withWall} from '../../kernel/prove.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {piecesAt,walkLive} from '../../core/count-recovery/live-dependencies.ts'
import {sub} from '../../core/solver.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {GuardObserver,type Packet} from './section9-guard-observer.ts'
import {packetHash} from './section9-ta-audit.ts'
let builder:((q:CountInst)=>{g:Goal,cert:Packet})|undefined
export const setSection10Builder=(value:NonNullable<typeof builder>)=>{builder=value}
export function section10Instance(ds:CountDecl[],cert:Packet):CountInst{
 const counts=countsForReads(ds,cert.reads);if(!counts)throw new Error('missing declarations')
 const a=cert.reads.findIndex(r=>r[0]==='r$4'),b=cert.reads.findIndex(r=>r[0]==='r$16')
 if(a<0||b<0||JSON.stringify(counts[a]!.below)!==JSON.stringify(counts[b]!.below))throw new Error('incompatible inclusion domains')
 if(cert.insts.some(q=>q.wit==='s10$inclusion'))throw new Error('witness collision')
 return {wit:'s10$inclusion',below:counts[a]!.below,terms:[[1,'r$4'],[-1,'r$16']],unit:0}
}
// Exact closure source projection, checked against the live closure for every
// original witness before using it on the one newly seeded witness.
function sourceFor(g:Goal,cert:Packet){
 const raw=g.hyps.slice(0,-cert.insts.length),ids=new Set(cert.reads.map(r=>r[0])),maps=new Set(cert.reads.map(r=>r[1])),wits=new Set(cert.insts.map(q=>q.wit))
 return (path:Path,witness?:string):C[]=>{
  const rows:{c:C,owner?:string}[]=[]
  for(const c of raw.flatMap(c=>piecesAt(c,path))){
   let skip=false;const owners=new Set<string>()
   walkLive(c,path,(o:any)=>{if(o.op==='get'&&maps.has(o.map)||o.op==='var'&&ids.has(o.name))skip=true;else if(o.op==='var'&&wits.has(o.name))owners.add(o.name)})
   if(!skip&&owners.size<=1)rows.push({c,owner:owners.values().next().value})
  }
  return rows.filter(r=>r.owner===undefined||r.owner===witness).map(r=>r.c)
 }
}
class InclusionObserver extends GuardObserver{
 override finish(){
  const original=this.contexts.findLast(c=>truth(same(x('a$#'),x('i')),c.scope)===true&&truth(less(x('j$'),x('i')),c.scope)===true&&!('tree'in c.q))
  if(!original||!builder)throw new Error('captured leaf or packet builder missing')
  const reference=JSON.parse(readFileSync('gap-input/B1.json','utf8')),base=reference.packet
  if(packetHash(original.g,original.cert,[...original.scope])!==packetHash(base.g,base.cert,base.scope))throw new Error('original captured packet changed')
  const guard:C={op:'<',a:{op:'get',map:'CT',key:x('i')},b:{op:'get',map:'CfgT',key:x('j$')}},a=linear(guard.a,original.scope),b=linear(guard.b,original.scope)
  if(!a||!b)throw new Error('unlinearized complement')
  const atom=sub(a,b);atom['1']=(atom['1']??0)+1
  const path:Path=new Map(original.scope).set(canon(atom),{lin:atom,holds:true})
  const projection=sourceFor(original.g,original.cert)
  for(const q of original.cert.insts)if(JSON.stringify(projection(path,q.wit))!==JSON.stringify(original.source(path,q.wit)))throw new Error('source projection mismatch')
  const added=section10Instance(original.ds,original.cert),next=builder(added),index=new Map(next.g.hyps.map((h,i)=>[JSON.stringify(h),i]))
  const remapped=new Map<LemmaCut,LemmaCut>(),remap=(lemma:LemmaCut):LemmaCut=>{
   const old=remapped.get(lemma);if(old)return old
   const slice=(lemma.slice??original.g.hyps.map((_,i)=>i)).map(i=>{const j=index.get(JSON.stringify(original.g.hyps[i]));if(j===undefined)throw new Error('old hypothesis missing after seed');return j})
   const out={...lemma,slice};remapped.set(lemma,out);return out
  }
  const c={...original,...next,source:sourceFor(next.g,next.cert),saved:original.saved.map(s=>({...s,lemma:remap(s.lemma)})),available:original.available.map(s=>({...s,lemma:remap(s.lemma)}))}
  this.indices=[...this.indices,this.full.insts.length];this.full={...this.full,insts:[...this.full.insts,added]}
  const model=reference.branches[0].queries.at(-1).model as Record<string,number>,numeric=c.numericFor(path,[])
  const modelValid=brokenOf(numeric)(model).length===0&&[...path.values()].every(v=>{const n=Object.entries(v.lin).reduce((s,[k,z])=>s+z*(k==='1'?1:model[k]!),0);return Number.isFinite(n)&&(v.holds?n<=0:n>0)})
  if(!modelValid)throw new Error('captured gap model does not satisfy live numeric projection')
  const row=this.pool(c).find(r=>r.inst.wit===added.wit)!,violated=brokenOf({name:'new inclusion',hyps:[row.good]})(model).length===1
  const before=fullWork(),start=performance.now()
  const result=withWall(start+60000,()=>counted(fullRate,()=>{
   const end=clock()+120,attempt=this.attempt(c,row.originalIndex,path,[],end,30)
   const numeric=attempt.saved?this.numeric(c,path,[attempt.saved],end):undefined
   return {attempt,numeric}
  },true))
  const units=(fullWork()-before)/fullRate,wallMs=performance.now()-start,keepsGuard=result.attempt.saved?.lemma.when.some(l=>canon(l)===canon(atom))??false
  const numericCore=result.numeric?.query.core?.length??(result.numeric?.numericProof?usedHyps(result.numeric.goal,result.numeric.numericProof,path).size:null),numericRefutes=result.numeric?.conditionalChecked===true
  const sourceRefutes=result.attempt.query.why===REFUTED||result.attempt.outcome==='checked'
  const pass=violated&&sourceRefutes&&(result.attempt.coreSize??Infinity)<=8&&result.attempt.queryCountedUnits<=30&&keepsGuard&&numericRefutes&&numericCore!==null&&numericCore<=6&&(result.numeric?.queryCountedUnits??Infinity)<=20&&units<=120
  const columns=[];for(let i=0;;i++){const e=columnTerm(`⟦${i}⟧`);if(e===undefined)break;columns.push(e)}
  console.log(JSON.stringify({test:'T-10A',columns,pass,stop:!pass,completeLawProof:false,modelReusedOnlyForNumericSelection:true,originalPacketHash:packetHash(base.g,base.cert,base.scope),sourceProjectionMatches:true,addedInstance:added,addedOriginalIndex:row.originalIndex,modelValid,instanceInViolatedSet:violated,guard,guardAtom:atom,keepsGuard,sourceRefutes,numericRefutes,numericCore,countedUnits:units,wallMs,...result,packet:{g:c.g,cert:c.cert,path:[...path],numeric,model},oldPacket:base}))
 }
}
export const s9=process.env.LAB_SECTION10_SIDE==='A'?new GuardObserver():new InclusionObserver()
