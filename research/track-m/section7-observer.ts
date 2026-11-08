// Section 7, T0 only: reference capture while proving; all audits run afterward.
import {gzipSync} from 'node:zlib'
import {type CountCert,type Goal,type Path,type Tree,check,truth} from '../../kernel/kernel.ts'
import {same,x} from '../../core/machine.ts'
import {brokenOf,clock,counted,fullRate,rowsAt,withWall} from '../../kernel/prove.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {refuteFast} from '../../core/solver.ts'
import {walkLive} from '../../core/count-recovery/live-dependencies.ts'
type Attempt={part:Goal,path:Path,index:number,scope:number,witness:string}
type Reuse=Attempt&{renamed:Goal,model:Record<string,number>,savedWitness:string}
let label='',cert:Pick<CountCert,'reads'|'insts'>
const attempts:Attempt[]=[],reuses:Reuse[]=[]
export const section7={
 begin(name:string,packet:Pick<CountCert,'reads'|'insts'>){label=name;cert=packet;attempts.length=0;reuses.length=0},
 attempt(part:Goal,path:Path,index:number,scope:number,witness:string){const q=cert.insts[index]!,pos=q.terms.find(([z])=>z===1),neg=q.terms.find(([z])=>z===-1),frame=q.terms.length===2&&cert.reads.find(r=>r[0]===pos?.[1])?.[1]==='bq#'&&cert.reads.find(r=>r[0]===neg?.[1])?.[1]==='bq';if(index===27||frame)attempts.push({part,path,index,scope,witness})},
 reuse(part:Goal,renamed:Goal,path:Path,index:number,scope:number,witness:string,savedWitness:string,model:Record<string,number>){reuses.push({part,renamed,path,index,scope,witness,savedWitness,model})},
 finish(){
  const audit=reuses.map(r=>{const vars=new Set<string>();walkLive(r.renamed.hyps,r.path,(o:any)=>{if(o.op==='var')vars.add(o.name)});const missing=[...vars].filter(v=>!Object.hasOwn(r.model,v)).sort((a,b)=>a.localeCompare(b));return {index:r.index,scope:r.scope,savedWitness:r.savedWitness,missing,legacyValid:brokenOf(r.renamed)(r.model).length===0}})
  // Match the same witness/fact, not index 27 (which is a partition in the canonical packet).
  const frames=attempts.filter(r=>cert.insts[r.index]!.wit==='frame$0')
  const selected=frames.filter(r=>truth(same(x('a$#'),x('i')),r.path)===true&&truth(same(x('j$'),x('i')),r.path)===true)
  const target=selected.find(r=>r.scope===7)??selected[0],start=performance.now()
  let direct:any
  if(target)direct=withWall(start+1000,()=>counted(fullRate,()=>{
   const before=clock(),q=modelSequence(target.path)(target.part,clock()+50),core=q.core??[],small={...target.part,hyps:core.map(i=>target.part.hyps[i]!)},fast=core.length?refuteFast(rowsAt(small,target.path),256):undefined
   const tree:Tree|undefined='tree'in q?q.tree:fast?.kind==='refuted'?{leaf:fast.steps}:undefined
   const checked=!!tree&&check('tree'in q?target.part:small,tree,target.path)
   return {index:target.index,scope:target.scope,hyps:target.part.hyps.length,instance:cert.insts[target.index],path:[...target.path],outcome:'tree'in q?'tree':q.stuck,why:'tree'in q?undefined:q.why,refuted:'tree'in q||q.why===REFUTED,core,checked,countedUnits:clock()-before,...(!('tree'in q)&&q.stuck==='sat'?{model:q.witness,modelValid:!!q.witness&&brokenOf(target.part)(q.witness).length===0}:{})}
  },true))
  console.log(JSON.stringify({test:'T0',label,framePool:cert.insts.flatMap((q,index)=>{const pos=q.terms.find(([z])=>z===1),neg=q.terms.find(([z])=>z===-1);return q.terms.length===2&&cert.reads.find(r=>r[0]===pos?.[1])?.[1]==='bq#'&&cert.reads.find(r=>r[0]===neg?.[1])?.[1]==='bq'?[{index,instance:q}]:[]}),reuses:audit.length,invalidatedByMissingBindings:audit.filter(a=>a.missing.length).length,audit,targetCandidates:selected.map(r=>({scope:r.scope,hyps:r.part.hyps.length})),direct,queryWallMs:performance.now()-start}))
  if(target)console.log(JSON.stringify({artifact:'T0-source',label,encoding:'gzip-base64',data:gzipSync(JSON.stringify({packet:cert,part:target.part,path:[...target.path],direct,reuses:reuses.filter(r=>r.index===27&&r.scope===target.scope).map(r=>({...r,path:[...r.path]}))})).toString('base64')}))
 }
}
