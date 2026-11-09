// Bounded observation of symbolic models, not a new high-budget proof census.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
import {join} from 'node:path'
import {type Machine,type Law,all,same,x,n} from '../../core/machine.ts'
import {finiteCountChoice} from '../../core/count-cases.ts'
import {countedAttempts,countsDump} from '../../core/counts.ts'
import {clock,counted,fullRate,fullWork,withDeadline,withWall} from '../../kernel/prove.ts'
import {checkMC,countedObligations,columnTerm} from '../../kernel/kernel.ts'
const [input,opText,out]=process.argv.slice(2)
if(!input||!out||!opText)throw Error('FAMILY OP OUT required')
const bytes=readFileSync(input),p=JSON.parse(bytes.toString()),op=Number(opText)
if(!p.generatorOnly||p.suppliedLaws?.length!==0||p.laws.length!==34)throw Error('original generated 34-law family required')
const choice=finiteCountChoice(p.m)
if(!choice||!Number.isInteger(op)||!choice[1].has(op))throw Error('operation absent from original machine')
const law:Law=p.laws[p.targets.star],m:Machine={...p.m,assume:all(...(p.m.assume?[p.m.assume]:[]),same(x(choice[0]),n(op)))}
if(!law)throw Error('missing Inv* target')
const captures:any[]=[],events:any[]=[],prior=countsDump.on
countsDump.on=event=>{const e=event as any;events.push({phase:e.phase,goal:e.goal,completion:e.completion,error:e.error});if(e.rawGoal||e.base)captures.push(e)}
const start=performance.now(),before=fullWork(),budget=6000,wall=7000
const result=(()=>{try{return withWall(start+wall,()=>counted(fullRate,()=>{const end=clock()+budget,attempt=countedAttempts(m,p.caller.map((i:number)=>p.laws[i]),new Set(p.support.map((i:number)=>p.laws[i])),end);attempt.houdini=true;return withDeadline(end,()=>attempt.traced(law,p.laws,0,budget))},true))}finally{countsDump.on=prior}})()
const proof='proof'in result?result.proof:undefined
const goals=proof?countedObligations(m,p.laws,{[law.name]:proof.instances},p.targets.star).filter(({goal})=>goal.name.endsWith('@step')):[]
const checked=!!proof&&goals.length>0&&goals.every(({goal,decls})=>!!proof.certs[goal.name]&&checkMC(goal.hyps,decls,proof.certs[goal.name]!))
const queries=captures.filter(e=>e.phase==='query'),model=captures.filter(e=>e.phase==='model').at(-1)
const record={researchOnly:true,scope:'original STEP under operation equality',familyHash:createHash('sha256').update(bytes).digest('hex'),familySize:p.laws.length,suppliedLaws:[],operation:{name:choice[0],value:op},pass:0,noShare:true,budget,wallAllowance:wall,units:(fullWork()-before)/fullRate,wallMs:performance.now()-start,checked,outcome:checked?'conditional-closed':'stuck'in result&&result.refuted?'certified-sat':'unknown',stuck:'stuck'in result?result.stuck:undefined,finiteReasons:events.filter(e=>e.completion).map(e=>e.completion),querySizes:queries.map(e=>e.hyps?.length),lastInstanceTermCounts:Object.fromEntries(Object.entries(model?.instances??{}).map(([k,v])=>[k,(v as unknown[]).length])),events:events.map(({phase,goal,error})=>({phase,goal,error}))}
const columns=[];for(let i=0;;i++){const term=columnTerm(`⟦${i}⟧`);if(term===undefined)break;columns.push(term)}
mkdirSync(out,{recursive:true});writeFileSync(join(out,'summary.json'),JSON.stringify(record,null,2)+'\n');writeFileSync(join(out,'capture.json.gz'),gzipSync(JSON.stringify({record,m,laws:p.laws,columns,captures,proof})))
console.log(JSON.stringify(record))
