// Exactly the five Track M probes, plus checked-tree hypothesis attribution.
import {readFileSync} from 'node:fs'
import {type Law, type Machine} from '../../core/machine.ts'
import {certFor} from '../../core/counts.ts'
import {proveFocusedCounts} from '../../core/count-focus-proof.ts'
import {assumed,countedObligations,checkMC,mcGoal} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,usedHyps,withWall} from '../../kernel/prove.ts'
const [input,prefix='one primary']=process.argv.slice(2),{m,laws}=JSON.parse(readFileSync(input!,'utf8')) as {m:Machine,laws:Law[]}
const index=laws.findIndex(l=>l.name.startsWith(prefix)),law=laws[index]!
if(index<0)throw new Error(`missing ${prefix}`)
const start=performance.now(),work=fullWork()
const proof=withWall(start+60000,()=>counted(fullRate,()=>proveFocusedCounts(m,laws,law,{},clock()+5000,(g,ds)=>certFor(g,ds,true,1000)),true))
const checked=!!proof&&countedObligations(m,laws,{[law.name]:proof.instances},index).every(p=>!!proof.certs[p.goal.name]&&checkMC(p.goal.hyps,p.decls,proof.certs[p.goal.name]!))
const wallMs=performance.now()-start,countedMs=(fullWork()-work)/fullRate
let usage: {complete:boolean,laws:Law[]}|null=null
if(proof&&checked){
 const needed=new Set<string>();let complete=true
 for(const {goal,decls} of countedObligations(m,laws,{[law.name]:proof.instances},index)){
  const cert=proof.certs[goal.name]!,expanded=mcGoal(goal.hyps,decls,cert),refs=expanded&&usedHyps(expanded,cert.tree)
  if(!refs){complete=false;continue}
  for(const i of refs)if(i<goal.hyps.length)needed.add(JSON.stringify(goal.hyps[i]))
 }
 usage={complete,laws:laws.filter(l=>assumed([l],proof.instances).some(h=>needed.has(JSON.stringify(h))))}
}
console.log(JSON.stringify({mode:'probe',law:law.name,proven:!!proof,checked,wallMs,countedMs,usage}))
