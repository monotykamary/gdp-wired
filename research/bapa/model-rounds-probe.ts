// One retained-law regression, not a protocol reseed or public acceptance.
import {readFileSync,writeFileSync} from 'node:fs'
import {installProfile} from './proof-worker.ts'
installProfile(process.env);process.env.GDP_MODELS_TRACE='1'
const {proveLaw,withModelRounds}=await import('../../kernel/prove.ts')
const {withBudget}=await import('../../core/wall.ts')
const {withPublicSearchPolicy}=await import('../../core/search-policy.ts')
const {workAdmissionSnapshot}=await import('../../core/work-admission.ts')
const {machine,family,index}=JSON.parse(readFileSync(new URL('./fixtures/retained7-model.json',import.meta.url),'utf8'))
const start=Date.now(),rounds:number[]=[],prior=console.error
console.error=(...args:unknown[])=>{
 const text=args.map(String).join(' '),match=/^\[models\] round (\d+) /.exec(text)
 if(match&&text.includes(family[index].name))rounds.push(Number(match[1]))
 prior(...args)
}
let result:unknown
try {
 result=withBudget(24_000_000_000,()=>
  withPublicSearchPolicy(false,()=>
   withModelRounds('progress',()=>proveLaw(machine,family,index))))
} catch(error) { result={error:String(error)} }
finally { console.error=prior }
const report={kind:'one retained-law regression',modelRounds:'progress',workBudget:24_000_000_000,publicCalls:0,protocolReseeds:0,elapsedMs:Date.now()-start,result,unconfirmedRounds:rounds,workSnapshot:workAdmissionSnapshot()}
writeFileSync(process.env.SUPERCOMPUTER_OUTPUT_DIR+'/round-probe.json',JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(report))
if(!result||typeof result!=='object'||!('proven' in result)||result.proven!==true||!rounds.includes(5))throw Error('retained:7 did not converge after more than four model refinements')
