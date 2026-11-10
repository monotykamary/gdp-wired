// Bounded pass-zero diagnostics, not an original-harness or no-share upper bound.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
import {all,same,x,n,type Machine} from '../../core/machine.ts'
import {countedAttempts,countsDump} from '../../core/counts.ts'
import {finiteCountChoice} from '../../core/count-cases.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
import {checkMC,countedObligations,columnTerm} from '../../kernel/kernel.ts'
const [file,tag,opText,out]=process.argv.slice(2)
if(!file||!tag||!out)throw Error('FAMILY TARGET OP OUTPUT')
const bytes=readFileSync(file),p=JSON.parse(bytes.toString()),op=Number(opText),choice=finiteCountChoice(p.m)
if(!p.generatorOnly||p.suppliedLaws?.length||!Number.isSafeInteger(op)||!choice?.[1].has(op))throw Error('invalid generated-family diagnostic')
const index=p.targets[tag],law=p.laws[index]
if(!law)throw Error('missing target')
const m:Machine={...p.m,assume:all(...(p.m.assume?[p.m.assume]:[]),same(x(choice[0]),n(op)))}
const budget=6000,wall=7000,phases:Record<string,number>={},tail:object[]=[],completions:object[]=[]
let symbolic:any,capture:object|undefined
mkdirSync(out,{recursive:true})
countsDump.on=(event)=>{
 const e=event as any,key=String(e.phase??'unknown');phases[key]=(phases[key]??0)+1
 const row={phase:e.phase,pass:e.pass,kind:e.kind,stuck:e.stuck,law:e.law,added:e.added}
 tail.push(row);if(tail.length>12)tail.shift()
 if(e.phase==='finite-model')completions.push({pass:e.pass,law:e.law,completion:e.completion?.genuine?{genuine:true}:e.completion})
 if(e.phase==='uncertified-model'||e.phase==='final-sat'){
  symbolic={stuck:e.stuck,keys:Object.keys(e.witness??{}).length,instances:Object.fromEntries(Object.entries(e.at??{}).map(([k,v])=>[k,Array.isArray(v)?v.length:0]))}
  const columns=[];for(let i=0;;i++){const t=columnTerm(`⟦${i}⟧`);if(t===undefined)break;columns.push(t)}
  capture={goal:e.goal,witness:e.witness,at:e.at,columns}
 }
}
const start=performance.now(),before=fullWork()
let result:ReturnType<ReturnType<typeof countedAttempts>['traced']>|undefined,error:string|undefined
try{counted(fullRate,()=>withWall(start+wall,()=>{
 const until=clock()+budget,attempt=countedAttempts(m,p.caller.map((i:number)=>p.laws[i]),new Set(p.support.map((i:number)=>p.laws[i])),until)
 attempt.houdini=true;result=attempt.traced(law,p.laws,0,budget)
}),true)}catch(e){error=String(e)}finally{countsDump.on=undefined}
const searchUnits=(fullWork()-before)/fullRate,searchWallMs=performance.now()-start
let checked=false
if(result&&'proof'in result){
 const proof=result.proof,goals=countedObligations(m,p.laws,{[law.name]:proof.instances},index).filter(({goal})=>goal.name.endsWith('@step'))
 checked=goals.length>0&&goals.every(({goal,decls})=>{const cert=proof.certs[goal.name];return !!cert&&checkMC(goal.hyps,decls,cert)})
}
let artifact:object|undefined
if(capture){const packed=gzipSync(JSON.stringify(capture)),path=join(out,'symbolic-model.json.gz');writeFileSync(path,packed);artifact={file:'symbolic-model.json.gz',bytes:packed.length,sha256:createHash('sha256').update(packed).digest('hex')}}
const record={diagnostic:'pass-zero-termination',conditional:true,generatorOnly:true,familySha256:createHash('sha256').update(bytes).digest('hex'),familySource:p.source,familySize:p.laws.length,suppliedLaws:[],law:law.name,op,pass:0,budget,wall,checked,result:result&&'stuck'in result?{stuck:result.stuck,refuted:result.refuted}:undefined,error,searchUnits,searchWallMs,completions,symbolic,phases,tail,artifact}
writeFileSync(join(out,'summary.json'),JSON.stringify(record,null,2)+'\n');console.log(JSON.stringify(record))
