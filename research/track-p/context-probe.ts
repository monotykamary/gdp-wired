// Captured production context only: no generator or whole-protocol execution.
import {readFileSync} from 'node:fs'
import {type Law,type Machine,walkOnce} from '../../core/machine.ts'
import {countedAttempts,countsDump} from '../../core/counts.ts'
import {readTuples} from '../../core/count-support.ts'
import {checkMC,countedObligations} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,withDeadline,withWall} from '../../kernel/prove.ts'
import {protocols} from '../protocols/ic3syn/models.ts'
const dir=process.argv[2]!,mode=process.argv[3]??'full',data=JSON.parse(readFileSync(dir+'/production.json','utf8')) as {machine:Machine,laws:Law[]},ref=JSON.parse(readFileSync(dir+'/family.json','utf8')) as {laws:Law[]},m=data.machine,all=data.laws
const p=protocols.find(p=>p.id==='paxos_epr')!,r=p.make(),callerNames=new Set([...r.kindLaws(),...p.laws(r)].map(l=>l.name)),caller=all.filter(l=>callerNames.has(l.name)),support=new Set(all.filter(l=>l.name.startsWith('carry:')||l.name.startsWith('scan-prefix:')))
const names=(value:unknown)=>{const out=new Set<string>();walkOnce(value,o=>{const q=o as Record<string,unknown>;if(q.op==='var'&&typeof q.name==='string')out.add(q.name)});return out}
const width=Math.max(1,...Object.values(m.step.maps??{}).map(w=>'each'in w?0:names(w.key).size))
const core=all.filter(l=>{
 if(caller.includes(l)||support.has(l))return true
 const reads=readTuples(l.holds);if(reads.some(([map])=>!!m.counts?.[map]))return true
 const bound=new Set([l.forall,...(l.keys??[]),...(l.some??[])]),free=[...names(l.holds)].filter(v=>!bound.has(v)&&Object.hasOwn(m.state,v))
 return !free.length&&reads.length>=2&&bound.size<=width
}),laws=mode==='core'?core:all,indices=process.argv.slice(4).map(Number),targets=indices.length?indices:[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74],ms=Number(process.env.REPLAY_MS??779)
console.log(JSON.stringify({mode,all:all.length,laws:laws.length,caller:caller.length,support:support.size,width,coreNames:core.map(l=>l.name)}))
const alpha=(law:Law)=>{const binders=new Map([law.forall,...(law.keys??[])].filter((n):n is string=>!!n).map((n,i)=>[n,'B'+i]));const walk=(v:unknown):unknown=>Array.isArray(v)?v.map(walk):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).map(([k,x])=>[k,k==='name'&&typeof x==='string'?binders.get(x)??x:walk(x)])):v;return JSON.stringify(walk(law.holds))}
const rows:object[]=[]
for(const index of targets){
 const law=laws.find(l=>alpha(l)===alpha(ref.laws[index]!));if(!law){rows.push({index,missing:true});continue}
 const events:object[]=[];countsDump.on=e=>{const q=e as Record<string,any>;events.push({phase:q.phase,pass:q.pass,hyps:q.hyps?.length,insts:q.certificateRequest?.insts?.length,generation:q.generation,error:q.error})}
 const start=performance.now(),out=withWall(start+4800,()=>counted(fullRate,()=>{const until=clock()+ms,attempts=countedAttempts(m,caller,support,until);attempts.houdini=true;return withDeadline(until,()=>{let answer=attempts.traced(law,laws,0,Math.max(0,until-clock()));if(!('proof'in answer)&&attempts.counted&&clock()<until)answer=attempts.traced(law,laws,1,Math.max(0,until-clock()));return answer})},true))
 let checked=false
 if('proof'in out)checked=countedObligations(m,laws,{[law.name]:out.proof.instances},laws.indexOf(law)).every(({goal,decls})=>checkMC(goal.hyps,decls,out.proof.certs[goal.name]!))
 const uses='proof'in out?Object.entries(out.proof.instances).filter(([,terms])=>terms.length).map(([name])=>name):undefined
 const row={index,status:'proof'in out?'proof':out.stuck,checked,ms:performance.now()-start,uses,events};rows.push(row);console.log(JSON.stringify(row))
}
countsDump.on=undefined;console.log(JSON.stringify({summary:true,mode,checked:rows.filter((r:any)=>r.checked).length,total:rows.length,rows}))
