// Research-only proof-directed admission over a captured candidate universe.
import {readFileSync} from 'node:fs'
import {type Law,type Machine,walkOnce} from '../../core/machine.ts'
import {countedAttempts,supportOrder,supportBudget,activeSupport} from '../../core/counts.ts'
import {checkCountedLaws,countedObligations,mcGoal,assumed} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,withDeadline,withWall,widen,usedHyps} from '../../kernel/prove.ts'
import {readTuples} from '../../core/count-support.ts'
import {protocols} from '../protocols/ic3syn/models.ts'
const data=JSON.parse(readFileSync(process.argv[2]!+'/production.json','utf8')) as {machine:Machine,laws:Law[]},m=data.machine,all=data.laws,p=protocols.find(p=>p.id==='paxos_epr')!,r=p.make(),names=new Set([...r.kindLaws(),...p.laws(r)].map(l=>l.name)),caller=all.filter(l=>names.has(l.name)),support=new Set(all.filter(l=>l.name.startsWith('carry:')||l.name.startsWith('scan-prefix:'))),narrow=process.argv[3]==='needed',precise=process.argv[4]==='used',warm=process.env.WARM_SUPPORT==='1',spine=process.env.DEFINITION_SPINE==='1'
const foundation=new Set(all.filter(l=>!l.keys?.length&&readTuples(l.holds).some(([map])=>!!m.counts?.[map])))
const sources=new Set(all.filter(l=>{
 const reads=readTuples(l.holds);if(reads.length<2||reads.some(([map])=>!!m.counts?.[map]))return false
 const bound=new Set([l.forall,...(l.keys??[])]);let zero=false,free=false
 walkOnce(l.holds,value=>{const q=value as any;if(q.op==='var'&&!bound.has(q.name)&&Object.hasOwn(m.state,q.name))free=true;if(q.op==='='&&(q.a?.op==='get'&&q.b?.op==='const'&&q.b.value===0||q.b?.op==='get'&&q.a?.op==='const'&&q.a.value===0))zero=true})
 return zero&&!free
}))
const start=performance.now(),events:object[]=[]
const result=withWall(start+60000,()=>counted(fullRate,()=>{
 const until=clock()+60000,attempts=countedAttempts(m,caller,support,until);attempts.houdini=true
 let universe=all.slice();const proofs=new Map<string,{proof:any,laws:Law[],deps:string[]}>()
 const uses=(proof:any,laws:Law[],owner:Law):string[]=>{
  const conservative=()=>laws.filter(l=>!l.forall||proof.instances[l.name]?.length).map(l=>l.name)
  if(!precise)return conservative()
  const used=new Set<string>()
  for(const {goal,decls}of countedObligations(m,laws,{[owner.name]:proof.instances},laws.indexOf(owner))){
   const cert=proof.certs[goal.name],expanded=mcGoal(goal.hyps,decls,cert),refs=expanded&&usedHyps(expanded,cert.tree)
   if(!refs)return conservative()
   for(const index of refs)if(index<goal.hyps.length)used.add(JSON.stringify(goal.hyps[index]))
  }
  return laws.filter(l=>assumed([l],proof.instances).some(h=>used.has(JSON.stringify(h)))).map(l=>l.name)
 }
 for(let round=0;round<200&&clock()<until&&performance.now()<start+60000;round++){
  const required=new Set([...caller.map(l=>l.name),...universe.filter(l=>warm&&support.has(l)||spine&&foundation.has(l)).map(l=>l.name),...(precise?[]:universe.filter(l=>!l.forall).map(l=>l.name))])
  for(const name of required){const known=proofs.get(name);if(known)for(const used of known.deps)if(universe.some(l=>l.name===used))required.add(used)}
  const ordered=supportOrder(universe,caller,support),todo=(spine?[...ordered.filter(l=>foundation.has(l)),...ordered.filter(l=>!foundation.has(l))]:ordered).filter(l=>required.has(l.name)&&!proofs.has(l.name))
  if(!todo.length){
   const kept=universe.filter(l=>required.has(l.name)),instances:Record<string,any>={},certs:Record<string,any>={}
   for(const law of kept){const saved=proofs.get(law.name)!;instances[law.name]=saved.proof.instances;const src=countedObligations(m,saved.laws,{[law.name]:saved.proof.instances},saved.laws.indexOf(law)),dst=countedObligations(m,kept,{[law.name]:saved.proof.instances},kept.indexOf(law));for(let i=0;i<dst.length;i++){const cert=saved.proof.certs[src[i]!.goal.name],a=mcGoal(src[i]!.goal.hyps,src[i]!.decls,cert),b=mcGoal(dst[i]!.goal.hyps,dst[i]!.decls,cert),tree=a&&b&&widen(a,b,cert.tree);if(!tree)return {checked:false,why:'lift',kept:kept.map(l=>l.name)};certs[dst[i]!.goal.name]={...cert,tree}}}
   return {checked:checkCountedLaws(m,kept,{instances,certs}),kept:kept.map(l=>l.name),proofs:proofs.size}
  }
  const law=todo[0]!,bounded=activeSupport(universe,support),share=(until-clock())/Math.max(1,universe.length-proofs.size),allotted=supportBudget(until-clock(),share,bounded&&caller.includes(law),support.has(law)&&!caller.includes(law)),end=Math.min(until,clock()+(bounded?Math.min(allotted,5000):allotted)),wall=Math.min(start+60000,performance.now()+4800)
  let out:any,context=universe
  const ask=(ls:Law[],limit:number)=>withWall(wall,()=>withDeadline(limit,()=>{let q=attempts.traced(law,ls,0,Math.min(allotted,Math.max(0,limit-clock())));if(!('proof'in q)&&attempts.counted&&clock()<limit)q=attempts.traced(law,ls,1,Math.min(allotted,Math.max(0,limit-clock())));return q}))
  if(narrow&&!caller.includes(law)&&required.size<universe.length){context=universe.filter(l=>required.has(l.name)||spine&&(support.has(l)||sources.has(l)));out=ask(context,Math.min(end,clock()+(end-clock())/3))}
  if(!out||!('proof'in out)){context=universe;out=ask(universe,end)}
  const deps='proof'in out?uses(out.proof,context,law):[]
  const event={law:law.name,budget:allotted,contextNames:context.map(l=>l.name),requiredNames:[...required],dependencies:deps,outcome:'proof'in out?'proof':out.stuck,context:context.length,required:required.size,kept:proofs.size,ms:performance.now()-start};events.push(event);console.log(JSON.stringify(event))
  if('proof'in out){proofs.set(law.name,{proof:out.proof,laws:context.slice(),deps});continue}
  if(caller.includes(law))return {checked:false,why:'caller failed',law:law.name}
  universe=universe.filter(l=>l!==law)
  for(const [name,saved]of proofs)if(saved.deps.includes(law.name))proofs.delete(name)
 }
 return {checked:false,why:'budget'}
},true))
console.log(JSON.stringify({summary:true,narrow,precise,warm,spine,ms:performance.now()-start,result,events}))
