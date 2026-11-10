// Research-only: the four count comparisons in MLDR-DESIGN §1.3's safety proof.
// Every claimed conditional result is checked by checkMC; this is not a full-set proof.
import {readFileSync} from 'node:fs'
import {certFor} from '../../core/counts.ts'
import {seedCountWitnessFlags} from '../../core/count-witness-flags.ts'
import {type CountCert, type Instances, countedObligations, mcGoal, checkMC} from '../../kernel/kernel.ts'
import {clock, counted, fullRate, fullWork, grow, instancesFor, triggered, withWall} from '../../kernel/prove.ts'
const [file,input,mode='closure'] = process.argv.slice(2)
const d=JSON.parse(readFileSync(file!,'utf8')), {m}=JSON.parse(readFileSync(input!,'utf8')), laws=d.laws, index=laws.findIndex((l:any)=>l.name===d.law)
let at:Instances={}
for(const [name,values] of Object.entries(d.at) as [string,any[]][]) {
  const n=name.startsWith('?')?1:1+(laws.find((l:any)=>l.name===name)?.keys?.length??0), kept=[]
  for(let i=0;i<values.length;i+=n) {const tuple=values.slice(i,i+n); if(!JSON.stringify(tuple).match(/"name":"w\$\d+"/)) kept.push(...tuple)}
  at[name]=kept
}
const first=countedObligations(m,laws,{[d.law]:at},index).find(g=>g.goal.name.endsWith('@step'))!
const reads=certFor(first.goal,first.decls,true,1000).reads
const ids=(map:string)=>reads.filter(r=>r[1]===map).map(r=>r[0]), ix=ids('inX')[0]!, count=ids('inS')[0]!, size=ids('cfgSize')[0]!
const terms:[number,string][][]=[[[1,ix],[-1,size]],[[1,size],[-1,ix]],...ids('bq').map(q=>[[1,count],[-1,q]] as [number,string][])]
const cert:Omit<CountCert,'tree'>={reads,insts:terms.map((terms,i)=>({wit:`mini$${i}`,below:first.decls[0]!.below,terms,unit:0}))}
const build=(at:Instances)=>{const b=countedObligations(m,laws,{[d.law]:at},index).find(g=>g.goal.name.endsWith('@step'))!;return {base:b,goal:{...b.goal,hyps:mcGoal(b.goal.hyps,b.decls,cert)!.hyps}}}
if(mode!=='raw') at=seedCountWitnessFlags(m,at,[{decls:first.decls,cert}])
if(mode==='closure') {at=instancesFor(m,laws,i=>[build(i).goal],{start:at,focus:['key$2#','key$3']});at=triggered(m,laws,at,i=>[build(i).goal],['key$2#','key$3'])}
const {base,goal}=build(at), t=performance.now(), w=fullWork()
const out=withWall(t+10000,()=>counted(fullRate,()=>grow(goal,new Map(),{nodes:0,until:clock()+5000}),true))
console.log(JSON.stringify({mode,hyps:goal.hyps.length,insts:cert.insts.length,instances:Object.fromEntries(Object.entries(at).map(([n,x])=>[n,x.length])),ms:Math.round(performance.now()-t),counted:Math.round((fullWork()-w)/fullRate),outcome:'tree' in out?'tree':out.stuck,checked:'tree' in out&&checkMC(base.goal.hyps,base.decls,{...cert,tree:out.tree})}))
