// Numerical consistency controls, not certified finite-state models.
import {readFileSync} from 'node:fs'
import {brotliDecompressSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {checkMC,mcGoal} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,grow,withWall} from '../../kernel/prove.ts'
const inputs=process.argv.slice(2)
if(!inputs.length||inputs.length>4)throw Error('one to four saved certificates required')
const results=withWall(performance.now()+12000,()=>counted(fullRate,()=>{
 const until=clock()+2700,results=[]
 for(const input of inputs){
  const bytes=readFileSync(input),p=JSON.parse(brotliDecompressSync(bytes).toString()),base={reads:p.cert.reads,insts:p.cert.insts},guard=(p.remainingOriginalIndices??p.hyps.map((_:unknown,i:number)=>i)).indexOf(16)
  if(p.kind!=='conditional-pointwise'||guard<0||!checkMC(p.hyps,p.decls,p.cert))throw Error('invalid conditional certificate or guard provenance')
  const before=fullWork(),check=(hyps:any[])=>{
   if(clock()>=until)throw Error('control budget exhausted')
   const goal=mcGoal(hyps,p.decls,base)
   if(!goal)throw Error('malformed control')
   const result=grow(goal,new Map(),{nodes:0,until:Math.min(until,clock()+250)})
   if('tree'in result||result.stuck!=='sat')throw Error('numerical context not confirmed SAT')
   return result.stuck
  }
  results.push({input,sha256:createHash('sha256').update(bytes).digest('hex'),inputSha256:p.inputSha256,control:p.control,scope:'numeric consistency only; NOT a finite-state model',guardedContext:check(p.hyps.slice(0,-1)),missingGuard:check(p.hyps.filter((_:unknown,i:number)=>i!==guard)),countedMs:(fullWork()-before)/fullRate})
 }
 return results
},true))
console.log(JSON.stringify(results))
