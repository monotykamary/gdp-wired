// One bounded pass-one STEP diagnostic; no changed candidates or trusted facts.
import {readFileSync,writeFileSync,appendFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
import {all,same,x,n,type Machine} from '../../core/machine.ts'
import {countedAttempts,countsDump} from '../../core/counts.ts'
import {finiteCountChoice} from '../../core/count-cases.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
import {checkMC,countedObligations} from '../../kernel/kernel.ts'
const [file,tag,opText,out]=process.argv.slice(2)
if(!file||!tag||!out)throw Error('FAMILY TARGET OP OUTPUT')
const bytes=readFileSync(file),p=JSON.parse(bytes.toString()),op=Number(opText),choice=finiteCountChoice(p.m)
if(!p.generatorOnly||p.suppliedLaws?.length||!Number.isSafeInteger(op)||!choice?.[1].has(op))throw Error('invalid generated-family diagnostic')
const index=p.targets[tag],law=p.laws[index]
if(!law)throw Error('missing target')
const m:Machine={...p.m,assume:all(...(p.m.assume?[p.m.assume]:[]),same(x(choice[0]),n(op)))}
const budget=6000,wall=7000,start=performance.now(),before=fullWork(),tail:object[]=[],phases:Record<string,number>={},active=new Map<number,string>()
mkdirSync(out,{recursive:true});const journal=join(out,'boundaries.jsonl')
let events=0,capped=false
countsDump.on=event=>{
 const e=event as any,phase=String(e.phase??'unlabelled');phases[phase]=(phases[phase]??0)+1
 if(e.phase==='boundary'){if(e.edge==='enter')active.set(e.id,e.span);else active.delete(e.id)}
 if(e.phase==='boundary-limit')capped=true
 const row={phase:e.phase,span:e.span,id:e.id,edge:e.edge,wallMs:performance.now()-start,units:(fullWork()-before)/fullRate,rss:process.memoryUsage().rss,params:e.phase==='model'?Object.fromEntries(p.m.params.map((k:string)=>[k,e.witness?.[k]])):undefined,error:typeof e.error==='string'?e.error.slice(0,512):undefined,completion:e.completion?.genuine?{genuine:true}:e.completion}
 if(events++<4096){appendFileSync(journal,JSON.stringify(row)+'\n');tail.push(row);if(tail.length>24)tail.shift()}else capped=true
}
let result:ReturnType<ReturnType<typeof countedAttempts>['traced']>|undefined,error:string|undefined
try{counted(fullRate,()=>withWall(start+wall,()=>{
 const until=clock()+budget,attempt=countedAttempts(m,p.caller.map((i:number)=>p.laws[i]),new Set(p.support.map((i:number)=>p.laws[i])),until)
 attempt.houdini=true;result=attempt.traced(law,p.laws,1,budget)
}),true)}catch(e){error=String(e)}finally{countsDump.on=undefined}
const searchUnits=(fullWork()-before)/fullRate,searchWallMs=performance.now()-start
let checked=false
if(result&&'proof'in result){const proof=result.proof,goals=countedObligations(m,p.laws,{[law.name]:proof.instances},index).filter(({goal})=>goal.name.endsWith('@step'));checked=goals.length>0&&goals.every(({goal,decls})=>{const cert=proof.certs[goal.name];return !!cert&&checkMC(goal.hyps,decls,cert)})}
const compressed=gzipSync(readFileSync(journal));writeFileSync(journal+'.gz',compressed)
const record={diagnostic:'pass-one-phase-boundaries',conditional:true,instrumented:true,familySha256:createHash('sha256').update(bytes).digest('hex'),familySize:p.laws.length,law:law.name,op,pass:1,budget,wall,checked,result:result&&'stuck'in result?{stuck:result.stuck,refuted:result.refuted}:undefined,error,searchUnits,searchWallMs,events,capped,active:[...active],phases,tail,journal:{bytes:compressed.length,sha256:createHash('sha256').update(compressed).digest('hex')}}
writeFileSync(join(out,'summary.json'),JSON.stringify(record,null,2)+'\n');console.log(JSON.stringify(record))
