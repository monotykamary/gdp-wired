// Untrusted support slicing. The resulting, weaker source context is checked
// normally; no dependency summary or reindexed tree is an acceptance result.
import {type Machine,type Law} from '../../core/machine.ts'
import {type CountCert,type CountDecl,type Goal,type Instances,type Path,type Tree,assumed,boundOf} from '../../kernel/kernel.ts'
import {usedHyps} from '../../kernel/prove.ts'
import {countedObligations,mcGoal,wallSpan} from './wall-profile.ts'
import {rebasePath} from './rebase-path.ts'
export function thinFlagInstances(m:Machine,goal:Goal,at:Instances,used:Set<number>):Instances{
 const out={...at}
 for(const [name,q]of Object.entries(m.step.flags??{})){
  if(q.op!=='all'||!at[`?${name}`]?.length)continue
  const key=`?${name}`,start=goal.hyps.findIndex(h=>h.op==='<='&&h.a.op==='var'&&h.a.name===key&&h.b.op==='const'&&h.b.value===1)
  if(start<0)continue
  const arity=boundOf(q).length,terms=at[key]!
  out[key]=Array.from({length:Math.floor(terms.length/arity)},(_,i)=>terms.slice(i*arity,(i+1)*arity)).filter((_,i)=>used.has(start+1+i)).flat()
 }
 return out
}
export function thinLawInstances(laws:Law[],goal:Goal,at:Instances,used:Set<number>):Instances{
 const rows=new Map<string,number[]>();goal.hyps.forEach((h,i)=>{const key=JSON.stringify(h),indices=rows.get(key)??[];indices.push(i);rows.set(key,indices)})
 const out={...at}
 for(const law of laws){
  const terms=at[law.name];if(!law.forall||!terms?.length)continue
  const arity=1+(law.keys?.length??0)
  out[law.name]=Array.from({length:Math.floor(terms.length/arity)},(_,i)=>terms.slice(i*arity,(i+1)*arity)).filter(tuple=>{
   const hs=assumed([law],{[law.name]:tuple}),indices=hs.flatMap(h=>rows.get(JSON.stringify(h))??[])
   return !indices.length||indices.some(i=>used.has(i))
  }).flat()
 }
 return out
}
export function thinSource(m:Machine,laws:Law[],index:number,at:Instances,base:{goal:Goal,decls:CountDecl[]},goal:Goal,cert:Omit<CountCert,'tree'>,tree:Tree,path:Path,until:number){
 const used=wallSpan('proof-dependencies',()=>usedHyps(goal,tree,path)),instances=thinLawInstances(laws,base.goal,thinFlagInstances(m,base.goal,at,used),used)
 const start=goal.hyps.length-cert.insts.length,insts=cert.insts.filter((_,i)=>used.has(start+i)),needed=new Set([...insts.flatMap(i=>i.terms.map(t=>t[1])),...(cert.picks??[]).map(p=>p[0])])
 const reads=cert.reads.filter((r,i)=>needed.has(r[0])||used.has(base.goal.hyps.length+i)),next={...cert,insts,reads}
 const source=countedObligations(m,laws,{[laws[index]!.name]:instances},index).find(g=>g.goal.name===base.goal.name)
 if(!source)return undefined
 const small=mcGoal(source.goal.hyps,source.decls,next)
 if(!small)return undefined
 // This exact-subset check is conservative: any shape change abandons the
 // proposal instead of treating dependency analysis as a proof rule.
 const original=new Set(goal.hyps.map(h=>JSON.stringify(h)))
 if(small.hyps.some(h=>!original.has(JSON.stringify(h))))return undefined
 const rebased=rebasePath(goal,tree,path,path,until,small)
 return rebased?{goal:small,tree:rebased,instances,cert:next,base:source,stats:{hypsBefore:goal.hyps.length,hypsAfter:small.hyps.length,instsBefore:cert.insts.length,instsAfter:insts.length,readsBefore:cert.reads.length,readsAfter:reads.length}}:undefined
}
