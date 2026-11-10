// Exercise the ordinary counted-attempt route, not a direct focused-helper call.
import {readFileSync} from 'node:fs'
import {type Law,type Machine} from '../../core/machine.ts'
import {countedAttempts} from '../../core/counts.ts'
import {checkMC,countedObligations} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
const start=performance.now(),work=fullWork(),[file,prefix='one primary']=process.argv.slice(2)
const {m,laws}=JSON.parse(readFileSync(file!,'utf8')) as {m:Machine,laws:Law[]}
const index=laws.findIndex(l=>l.name.startsWith(prefix)),law=laws[index]
if(!law)throw new Error(`law not found: ${prefix}`)
const result=withWall(start+60000,()=>counted(fullRate,()=>{
 const until=clock()+5000,attempts=countedAttempts(m,laws,new Set(),until)
 let result=attempts.traced(law,laws,0,Math.max(0,until-clock()))
 if(!('proof'in result)&&attempts.counted&&clock()<until)result=attempts.traced(law,laws,1,Math.max(0,until-clock()))
 const checked='proof'in result&&countedObligations(m,laws,{[law.name]:result.proof.instances},index).every(p=>!!result.proof.certs[p.goal.name]&&checkMC(p.goal.hyps,p.decls,result.proof.certs[p.goal.name]!))
 return {proven:'proof'in result,checked,...('stuck'in result?{stuck:result.stuck}:{})}
},true))
console.log(JSON.stringify({mode:'ordinary-route',law:law.name,...result,wallMs:performance.now()-start,countedMs:(fullWork()-work)/fullRate}))
