// Cold-start refinement using only focused pairs and ordinary MBQI.
import {readFileSync} from 'node:fs'
import {type E,walkOnce,x} from '../../core/machine.ts'
import {type Instances,countedObligations,mcGoal,checkMC} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,grow,modelInstances,withWall} from '../../kernel/prove.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {certFor} from '../../core/counts.ts'
import {countLawSeeds,fieldLawBridges,focusCountCert} from '../../core/count-focused.ts'
import {seedCountWitnessFlags} from '../../core/count-witness-flags.ts'
const [file,input,mode='cold']=process.argv.slice(2),d=JSON.parse(readFileSync(file!,'utf8')),{m}=JSON.parse(readFileSync(input!,'utf8')),ls=d.laws,idx=ls.findIndex((l:any)=>l.name===d.law),law=ls[idx]
const own:E[]=[...law.forall?[x(`${law.forall}#`)]:[],...(law.keys??[]).map(x)],keys:E[]=[]
walkOnce([m.step,m.assume],(o:any)=>{if(o.op==='get')keys.push(o.key)})
for(const w of Object.values(m.step.maps??{}) as any[])if(w.key)keys.push(w.key)
const request:E[]=m.inputs.filter((name:string)=>Object.values(m.counts??{}).some((d:any)=>![d.j,d.lo,d.key].includes(name)&&JSON.stringify([d.below,d.body]).includes(`"name":${JSON.stringify(name)}`))).map(x)
let at:Instances=Object.fromEntries(Object.entries(m.step.flags??{}).filter(([,q]:any)=>q.op==='all'&&!q.keys?.length).map(([name])=>[`?${name}`,[...own,...request]]))
if(law.forall)at[law.name]=own
if(mode==='warm') {
  at={}
  for(const [name,values] of Object.entries(d.at) as [string,E[]][]){
    const l=ls.find((l:any)=>l.name===name),n=l?1+(l.keys?.length??0):1,keep:E[]=[]
    for(let i=0;i<values.length;i+=n){const tuple=values.slice(i,i+n);if(!/"name":"w(?:\$\d+|\?)/.test(JSON.stringify(tuple)))keep.push(...tuple)}
    at[name]=keep
  }
  const names=[law.forall,...law.keys??[]], scalar=new Set<string>()
  walkOnce(law.holds,(o:any)=>{if(o.op==='get'&&o.key.op==='var')scalar.add(o.key.name)})
  const rows=own.filter((_,i)=>scalar.has(names[i]))
  at=countLawSeeds(m,ls,at,rows.length?rows:own,request,true)
  at=fieldLawBridges(m,ls,at,rows.length?rows:own,request,own.length===3?own[2]:undefined)
} else at=countLawSeeds(m,ls,at,own,request)
const build=()=>{
  const base=countedObligations(m,ls,{[law.name]:at},idx).find(g=>g.goal.name.endsWith('@step'))!
  const cert=focusCountCert(m,base.decls,certFor(base.goal,base.decls,true,1000),mode==='warm'?{carried:m.inputMaps[0],structural:false}:{})
  const seeded=seedCountWitnessFlags(m,at,[{decls:base.decls,cert}],true)
  if(seeded!==at){at=seeded;return undefined}
  return {base,cert,goal:{...base.goal,hyps:mcGoal(base.goal.hyps,base.decls,cert)!.hyps}}
}
const seq=modelSequence(),start=performance.now(),w=fullWork(),trace:object[]=[]
const out=withWall(start+10000,()=>counted(fullRate,()=>{
  const end=clock()+5000
  for(let round=0;round<30&&clock()<end;round++){
    const b=build()??build()!
    const q=seq(b.goal,Math.min(end,clock()+750))
    trace.push({round,hyps:b.goal.hyps.length,insts:b.cert.insts.length,query:'tree'in q?'tree':q.stuck,why:'tree'in q?undefined:q.why})
    if(!('tree'in q)&&q.stuck==='sat'&&q.witness){
      const added=modelInstances(m,ls,at,b.goal,q.witness)
      if(added){at=added;continue}
      return {outcome:'sat',witness:q.witness}
    }
    const proof=grow(b.goal,new Map(),{nodes:0,until:end})
    if('tree'in proof)return {outcome:'tree',checked:checkMC(b.base.goal.hyps,b.base.decls,{...b.cert,tree:proof.tree})}
    if(proof.stuck==='sat'&&proof.witness){const added=modelInstances(m,ls,at,b.goal,proof.witness);if(added){at=added;continue}}
    return {outcome:proof.stuck,witness:proof.witness}
  }
  return {outcome:'unknown'}
},true))
console.log(JSON.stringify({file,law:law.name,...out,counted:Math.round((fullWork()-w)/fullRate),wall:Math.round(performance.now()-start),trace}))
