// Research-only: determine which fixtures exercise completion and yield checked proofs.
import {type Law,type Machine,get,n,x,ite,same} from '../../core/machine.ts'
import {countedAttempts,countsDump} from '../../core/counts.ts'
import {clock,counted,fullRate,withDeadline,withWall} from '../../kernel/prove.ts'
import {checkMC,countedObligations} from '../../kernel/kernel.ts'
for(const body of ['raw','bit'] as const)for(const limit of [1,2])for(const kind of ['count','field'] as const){
 const m:Machine={name:'completion probe',params:[],inputs:[],state:{},maps:{Cells:0},counts:{Total:{j:'countRow',key:'member',below:n(2),body:body==='raw'?get('Cells',x('member')):ite(same(get('Cells',x('member')),n(1)),n(1),n(0))}},step:{}}
 const law:Law={name:'bounded '+kind,forall:'row',holds:{op:'<=',a:get(kind==='count'?'Total':'Cells',x('row')),b:n(limit)}}
 const events:{phase:unknown,added?:number}[]=[],prior=countsDump.on
 try{
  countsDump.on=e=>{if('phase'in e)events.push({phase:e.phase,...('added'in e&&Array.isArray(e.added)?{added:e.added.length}:{})})}
  const result=withWall(performance.now()+3000,()=>counted(fullRate,()=>{const until=clock()+1000;return withDeadline(until,()=>countedAttempts(m,[law],new Set(),until).traced(law,[law],1,1000))},true))
  let checked=false
  if('proof'in result)checked=countedObligations(m,[law],{[law.name]:result.proof.instances},0).every(({goal,decls})=>checkMC(goal.hyps,decls,result.proof.certs[goal.name]!))
  console.log('COMPLETION_FIXTURE '+JSON.stringify({body,limit,kind,result:'proof'in result?'proof':result,checked,events}))
 }finally{countsDump.on=prior}
}
// A concrete-key target with the same bounded universal premise; conditional certificates remain kernel-checked.
for(const guarded of [false,true]){
 const m:Machine={name:'concrete completion probe',params:[],inputs:[],state:{ready:n(0)},maps:{Cells:0},counts:{Total:{j:'countRow',key:'member',below:n(2),body:ite(same(get('Cells',x('member')),n(1)),n(1),n(0))}},step:{state:{ready:n(1)}}}
 const bound={op:'<=' as const,a:get('Total',n(0)),b:n(2)},law:Law={name:'bounded target',holds:guarded?{op:'or',xs:[same(x('ready'),n(0)),bound]}:bound},premise:Law={name:'bounded source',forall:'row',holds:{op:'<=',a:get('Total',x('row')),b:n(2)}},family=[law,premise]
 const events:{phase:unknown,added?:number}[]=[],prior=countsDump.on
 try{
  countsDump.on=e=>{if('phase'in e)events.push({phase:e.phase,...('added'in e&&Array.isArray(e.added)?{added:e.added.length}:{})})}
  const result=withWall(performance.now()+3000,()=>counted(fullRate,()=>{const until=clock()+1000;return withDeadline(until,()=>countedAttempts(m,family,new Set(),until).traced(law,family,1,1000))},true))
  let checked=false
  if('proof'in result)checked=countedObligations(m,family,{[law.name]:result.proof.instances},0).every(({goal,decls})=>checkMC(goal.hyps,decls,result.proof.certs[goal.name]!))
  console.log('COMPLETION_POSITIVE '+JSON.stringify({guarded,result:'proof'in result?'proof':result,checked,events}))
 }finally{countsDump.on=prior}
}
