// Diagnostic only: test whether a proposed positive fixture has a checked proof.
import {readFileSync,mkdtempSync,rmSync} from 'node:fs'
import {resolve,join} from 'node:path'
const {restore,command}=await import(resolve('research/verify-all/final-gate-common.ts'))
const fix=JSON.parse(readFileSync('regression-driver/paxos-fix.json','utf8')).candidate
const temp=mkdtempSync('/tmp/lane-i-count-fixtures-')
try{for(const revision of ['bf01190119f9409077a36e11a4a5b763fb6c1cad',fix]){
 const dest=join(temp,revision);restore(resolve('paxos-input'),dest,revision);command('bun',['install','--frozen-lockfile'],dest)
 const {n,x,get,same,ite}=await import(join(dest,'core/machine.ts'))
 const {countedAttempts,countsDump}=await import(join(dest,'core/counts.ts'))
 const {clock,counted,fullRate,withDeadline,withWall}=await import(join(dest,'kernel/prove.ts'))
 const {countedObligations,checkMC}=await import(join(dest,'kernel/kernel.ts'))
 for(const variant of ['zero-equality','constant-upper-bound','conditional-two','conditional-three']){
  const conditional=variant.startsWith('conditional'),bound=variant==='conditional-three'?3:2
  const m={name:'count fixture probe',params:[],inputs:[],state:conditional?{ready:n(0)}:{},maps:conditional?{Cells:0}:{},counts:{Total:{j:'countRow',key:'member',below:n(bound),body:conditional?ite(same(get('Cells',x('member')),n(1)),n(1),n(0)):n(0)}},step:conditional?{state:{ready:n(1)}}:{}}
  const limit=(key:any)=>variant==='zero-equality'?same(get('Total',key),n(0)):{op:'<=',a:get('Total',key),b:n(bound)}
  const law={name:'bounded target',holds:conditional?{op:'or',xs:[same(x('ready'),n(0)),limit(n(0))]}:limit(n(0))},premise={name:'bounded source',forall:'row',holds:limit(x('row'))},family=[law,premise],phases:string[]=[]
  const prior=countsDump.on
  try{
   countsDump.on=(event:any)=>{if(typeof event.phase==='string')phases.push(event.phase)}
   const result=withWall(performance.now()+3000,()=>counted(fullRate,()=>{const until=clock()+1000;return withDeadline(until,()=>countedAttempts(m,family,new Set(),until).traced(law,family,1,1000))},true))
   const proven='proof'in result,checks=proven?[...countedObligations(m,family,{[law.name]:result.proof.instances},0)].map(({goal,decls}:any)=>checkMC(goal.hyps,decls,result.proof.certs[goal.name]!)):[]
   console.log('PAXOS_FIXTURE_PROBE '+JSON.stringify({revision,variant,proven,stuck:result.stuck,checks,phases}))
  }finally{countsDump.on=prior}
 }
}}finally{rmSync(temp,{recursive:true,force:true})}
