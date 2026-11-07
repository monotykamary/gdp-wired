import {readFileSync} from 'node:fs'
import {certFor} from '../../core/counts.ts'
import {proveFocusedCounts} from '../../core/count-focus-proof.ts'
import {countedObligations,checkMC} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
const [input,prefix='Inv1758']=process.argv.slice(2),{m,laws}=JSON.parse(readFileSync(input!,'utf8')),index=laws.findIndex((l:any)=>l.name.startsWith(prefix)),law=laws[index]
if(!law)throw new Error('law not found')
const start=performance.now(),work=fullWork(),trace:Record<string,unknown>[]=[]
const result=withWall(start+60000,()=>counted(fullRate,()=>{
 const proof=proveFocusedCounts(m,laws,law,{},clock()+5000,(goal,decls)=>certFor(goal,decls,true,1000),event=>trace.push(event))
 return {proven:!!proof,checked:!!proof&&countedObligations(m,laws,{[law.name]:proof.instances},index).every(p=>!!proof.certs[p.goal.name]&&checkMC(p.goal.hyps,p.decls,proof.certs[p.goal.name]!))}
},true))
console.log(JSON.stringify({law:law.name,...result,trace,counted:Math.round((fullWork()-work)/fullRate),wall:Math.round(performance.now()-start)}))
