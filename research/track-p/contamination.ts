// Diagnostic only: add one generic source to a known checked-family control.
// No family IDs or results from this script are consumed by production.
import {existsSync,readFileSync} from 'node:fs'
import {type Law,type Machine,walkOnce} from '../../core/machine.ts'
import {countedAttempts,countsDump} from '../../core/counts.ts'
import {readTuples} from '../../core/count-support.ts'
import {checkMC,countedObligations} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,withDeadline,withWall} from '../../kernel/prove.ts'
import {definitionContext} from './definition-context.ts'
import {frameContext} from './frame-context.ts'
import {protocols} from '../protocols/ic3syn/models.ts'
const dir=process.argv[2]!,part=Number(process.argv[3]??0),data=JSON.parse(readFileSync(dir+'/production.json','utf8')) as {machine:Machine,laws:Law[]},ref=JSON.parse(readFileSync(dir+'/family.json','utf8')) as {laws:Law[]},m=data.machine,omitted=new Set<string>(JSON.parse(process.env.OMIT_LAWS?readFileSync(process.env.OMIT_LAWS,'utf8'):'[]')),all=data.laws.filter(l=>!omitted.has(l.name)),ms=Number(process.env.REPLAY_MS??779)
const p=protocols.find(p=>p.id==='paxos_epr')!,r=p.make(),callerNames=new Set([...r.kindLaws(),...p.laws(r)].map(l=>l.name)),caller=all.filter(l=>callerNames.has(l.name)),support=new Set(all.filter(l=>l.name.startsWith('carry:')||l.name.startsWith('scan-prefix:')))
const alpha=(law:Law)=>{const binders=new Map([law.forall,...(law.keys??[])].filter((n):n is string=>!!n).map((n,i)=>[n,'B'+i]));const walk=(v:unknown):unknown=>Array.isArray(v)?v.map(walk):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).map(([k,x])=>[k,k==='name'&&typeof x==='string'?binders.get(x)??x:walk(x)])):v;return JSON.stringify(walk(law.holds))}
const indices=[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74],base=indices.map(i=>{const l=all.find(l=>alpha(l)===alpha(ref.laws[i]!));if(!l)throw Error('missing '+i);return l}),target=base[indices.indexOf(Number(process.env.TARGET_INDEX??11))]!,late=existsSync(dir+'/late-context.json')?new Set<string>(JSON.parse(readFileSync(dir+'/late-context.json','utf8'))):undefined
const names=(value:unknown)=>{const out=new Set<string>();walkOnce(value,o=>{const q=o as Record<string,unknown>;if(q.op==='var'&&typeof q.name==='string')out.add(q.name)});return out},width=Math.max(1,...Object.values(m.step.maps??{}).map(w=>'each'in w?0:names(w.key).size))
const core=all.filter(l=>{if(caller.includes(l)||support.has(l))return true;const reads=readTuples(l.holds);if(reads.some(([map])=>!!m.counts?.[map]))return true;const bound=new Set([l.forall,...(l.keys??[]),...(l.some??[])]),free=[...names(l.holds)].filter(v=>!bound.has(v)&&Object.hasOwn(m.state,v));return !free.length&&reads.length>=2&&bound.size<=width}),extra=core.filter(l=>!base.includes(l)),cases=[{label:'base-reference-order',laws:base},{label:'base',laws:all.filter(l=>base.includes(l))},...(part===0||process.env.CONTEXT_CONTROL==='1'?[{label:'core',laws:core},{label:'all',laws:all},{label:'definition',laws:definitionContext(m,all,target,support)},{label:'frame',laws:frameContext(m,all,target,support)},...(late?[{label:'late',laws:all.filter(l=>late.has(l.name))},{label:'late-definition',laws:definitionContext(m,all.filter(l=>late.has(l.name)),target,support)}]:[])]:[]),...extra.flatMap((l,i)=>i%4===part?[{label:l.name,laws:all.filter(law=>base.includes(law)||law===l)}]:[])]
const rows:object[]=[]
for(const {label,laws}of cases){
 let first:unknown,last:unknown,error:unknown
 countsDump.on=e=>{const q=e as Record<string,any>;if(q.error)error=q.error;if(q.phase==='query'&&q.pass===1){last=JSON.parse(JSON.stringify({hyps:q.hyps?.length,seedCount:q.seedCount,generation:q.generation,instances:q.instances,certificateRequest:q.certificateRequest}));first??=last}}
 const start=performance.now(),out=withWall(start+4800,()=>counted(fullRate,()=>{const until=clock()+ms,a=countedAttempts(m,caller,support,until);a.houdini=true;return withDeadline(until,()=>{const first=process.env.COUNT_FIRST==='1'?1:0;let q=a.traced(target,laws,first,Math.max(0,until-clock()));if(!('proof'in q)&&(first||a.counted)&&clock()<until)q=a.traced(target,laws,first?0:1,Math.max(0,until-clock()));return q})},true))
 const checked='proof'in out&&countedObligations(m,laws,{[target.name]:out.proof.instances},laws.indexOf(target)).every(({goal,decls})=>checkMC(goal.hyps,decls,out.proof.certs[goal.name]!)),row={label,part,laws:laws.length,checked,status:'proof'in out?'proof':out.stuck,ms:performance.now()-start,error,first,last};rows.push(row);console.log(JSON.stringify(row))
}
countsDump.on=undefined;console.log(JSON.stringify({summary:true,part,base:base.length,core:core.length,extra:extra.length,rows:rows.map(({first:_first,last:_last,...row}:any)=>row)}))
