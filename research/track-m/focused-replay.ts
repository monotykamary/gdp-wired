// Generic focused pair proposal on an archived conditional induction goal.
import {readFileSync} from 'node:fs'
import {type E, walkOnce, x} from '../../core/machine.ts'
import {certFor} from '../../core/counts.ts'
import {countLawSeeds, focusCountCert} from '../../core/count-focused.ts'
import {seedCountWitnessFlags} from '../../core/count-witness-flags.ts'
import {type Instances, checkMC, countedObligations, mcGoal} from '../../kernel/kernel.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {clock, counted, fullRate, fullWork, grow, withWall} from '../../kernel/prove.ts'
const [file,input,mode='warm',family]=process.argv.slice(2), d=JSON.parse(readFileSync(file!,'utf8')), {m}=JSON.parse(readFileSync(input!,'utf8')), laws=d.laws, index=laws.findIndex((l:any)=>l.name===d.law)
let at:Instances={}
for(const [name,values] of Object.entries(d.at) as [string,any[]][]) {
  const n=name.startsWith('?')?1:1+(laws.find((l:any)=>l.name===name)?.keys?.length??0), kept=[]
  for(let i=0;i<values.length;i+=n) {const tuple=values.slice(i,i+n); if(!JSON.stringify(tuple).match(/"name":"w\$\d+"/)) kept.push(...tuple)}
  at[name]=kept
}
if(mode==='cold') {
  const law=laws[index], own:E[]=[...law.forall?[x(`${law.forall}#`)]:[],...(law.keys??[]).map(x)], keys:E[]=[]
  walkOnce([m.step,m.assume],(o:any)=>{if(o.op==='get')keys.push(o.key)})
  for(const w of Object.values(m.step.maps??{}) as any[])if(w.key)keys.push(w.key)
  const request:E[]=m.inputs.filter((name:string)=>keys.some(e=>JSON.stringify(e).includes(`"name":${JSON.stringify(name)}`))).map(x)
  at=Object.fromEntries(Object.entries(m.step.flags??{}).filter(([,q]:any)=>q.op==='all'&&!q.keys?.length).map(([name])=>[`?${name}`,[...own,...request]]))
  if(law.forall)at[law.name]=own
  at=countLawSeeds(m,laws,at,own,request)
}
const first=countedObligations(m,laws,{[d.law]:at},index).find(g=>g.goal.name.endsWith('@step'))!
const full=certFor(first.goal,first.decls,true,1000)
let cert=focusCountCert(m,first.decls,full,family===undefined?{}:{carried:m.inputMaps[Number(family)],structural:false})
const selection={counted:0,status:'unused',proposed:cert.insts.length}
if(mode==='core') {
  // Speculatively assume just each CInst's linear alternative to find a small
  // candidate set. No verdict uses this abstraction: the selected original
  // witness-bearing CInsts must still pass checkMC below.
  const g=mcGoal(first.goal.hyps,first.decls,cert)!,start=g.hyps.length-cert.insts.length
  const abstract={...g,hyps:g.hyps.map((c,i)=>i>=start&&c.op==='or'?c.xs[0]!:c)},before=fullWork()
  const q=withWall(performance.now()+2000,()=>counted(fullRate,()=>modelSequence()(abstract,clock()+750),true))
  selection.counted=Math.round((fullWork()-before)/fullRate)
  selection.status='tree'in q?'tree':q.why??q.stuck
  if(!('tree'in q)&&q.why===REFUTED&&q.core) {
    const used=new Set(q.core);cert={...cert,insts:cert.insts.filter((_,i)=>used.has(start+i))}
  }
}
at=seedCountWitnessFlags(m,at,[{decls:first.decls,cert}])
const base=countedObligations(m,laws,{[d.law]:at},index).find(g=>g.goal.name.endsWith('@step'))!, goal={...base.goal,hyps:mcGoal(base.goal.hyps,base.decls,cert)!.hyps}
const t=performance.now(), w=fullWork(), out=withWall(t+10000,()=>counted(fullRate,()=>grow(goal,new Map(),{nodes:0,until:clock()+Math.max(0,5000-selection.counted)}),true))
console.log(JSON.stringify({file,law:d.law,family,selection,hyps:goal.hyps.length,insts:cert.insts.length,ms:Math.round(performance.now()-t),counted:selection.counted+Math.round((fullWork()-w)/fullRate),outcome:'tree' in out?'tree':out.stuck,checked:'tree' in out&&checkMC(base.goal.hyps,base.decls,{...cert,tree:out.tree}),...!('tree' in out)?{witness:out.witness}: {}}))
