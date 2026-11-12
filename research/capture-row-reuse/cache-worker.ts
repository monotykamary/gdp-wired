// Exact old/new cache result and work-trace comparison in fresh processes.
import {createHash} from 'node:crypto'
import {type Goal,type Path,type Tree,canon,leafConstraints} from '../../kernel/kernel.ts'
import {less,n,x} from '../../core/machine.ts'
import {slicedCheck,conditionalProofStats} from '../../core/count-recovery/conditional-check-cache.ts'
import {slicedCheck as oldCheck,conditionalProofStats as oldStats} from './reference-conditional-check-cache.ts'
import {BudgetExpired,workLedger,withWorkAdmissionTrace} from '../../core/work-admission.ts'
import {workAmount} from '../../core/work-amount.ts'
const mode=process.argv[2];if(mode!=='reference'&&mode!=='reuse')throw Error('invalid cache mode')
const check=mode==='reference'?oldCheck:slicedCheck,stats=mode==='reference'?oldStats:conditionalProofStats
const goal:Goal={name:'cache identity',hyps:[less(x('x'),n(0))]},path:Path=new Map()
for(let i=0;i<20;i++){const lin={['guard'+i]:1};path.set(canon(lin),{lin,holds:true})}
const rows=leafConstraints(goal,path),fact=rows.findIndex(r=>r.src&&'fact'in r.src),nat=rows.findIndex(r=>r.src&&'nat'in r.src&&r.src.nat==='x')
const tree:Tree={leaf:[{kind:'input',index:fact},{kind:'input',index:nat},{kind:'combine',a:0,b:1,ma:1,mb:1}]},bad:Tree={leaf:[{kind:'input',index:fact}]}
const equivalent=():Path=>new Map([...path].map(([k,a])=>[k,{lin:{...a.lin},holds:a.holds}]))
const reversed:Path=new Map([...path].reverse()),aliased:Path=new Map(path);aliased.set('@duplicate',{lin:{guard0:1},holds:true})
const outputs:unknown[]=[],digest=createHash('sha256')
workLedger.withBudget(workAmount(100000000n),()=>withWorkAdmissionTrace(e=>digest.update(JSON.stringify(e)),()=>{
 for(const [proof,p]of [[tree,path],[tree,equivalent()],[tree,path],[bad,path],[bad,equivalent()],[tree,reversed],[tree,aliased],[tree,equivalent()],[tree,new Map()],[tree,new Map()],[{...tree},path]] as const){
  const before=stats(),answer=check(goal,proof,p),after=stats()
  outputs.push({answer,delta:Object.fromEntries(Object.keys(before).map(k=>[k,after[k as keyof typeof after]-before[k as keyof typeof before]]))})
 }
}))
const interruptions:unknown[]=[]
for(const grant of [0n,1n,2n,5n,20n]){
 const g:Goal={...goal},t:Tree={...tree},p:Path=new Map()
 for(let i=0;i<20;i++)p.set('limit'+i,{lin:{['limit'+grant+'_'+i]:1},holds:true})
 const trace=createHash('sha256');let error:unknown,answer:boolean|undefined,recovered=false
 workLedger.withBudget(workAmount(grant),()=>withWorkAdmissionTrace(e=>trace.update(JSON.stringify(e)),()=>{
  try{answer=check(g,t,p)}catch(e){error=e}
 }))
 workLedger.withBudget(workAmount(100000000n),()=>withWorkAdmissionTrace(e=>trace.update(JSON.stringify(e)),()=>{recovered=check(g,t,p)}))
 interruptions.push({grant:String(grant),answer:answer??null,recovered,trace:trace.digest('hex'),error:error instanceof Error?{name:error.name,message:error.message,phase:error instanceof BudgetExpired?error.phase:null,capacity:workLedger.capacityRefusal(error)??null}:null})
}
console.log(JSON.stringify({outputs,interruptions,trace:digest.digest('hex'),counters:workLedger.snapshot().counters}))
