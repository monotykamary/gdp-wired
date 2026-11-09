// A per-law cost diagnostic, not an accepted jointly checked family.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {gzipSync} from 'node:zlib'
import {countedAttempts,countsDump,cprof} from '../../core/counts.ts'
import {clock,counted,fullRate,fullWork,withDeadline,withWall} from '../../kernel/prove.ts'
import {checkMC,columnTerm,countedObligations} from '../../kernel/kernel.ts'
const [input,tag,out,budgetArg='2700']=process.argv.slice(2),p=JSON.parse(readFileSync(input!,'utf8')),index=p.targets[tag!],law=p.laws[index],budget=Number(budgetArg)
if(!law||!out||!(budget>0&&budget<=5000))throw Error('FAMILY TARGET OUTPUT [budget <=5000]')
mkdirSync(out,{recursive:true});const events:any[]=[],captures:any[]=[]
countsDump.on=e=>{const v=e as any;events.push({phase:v.phase,pass:v.pass,goal:v.goal,law:v.law,hyps:v.hyps?.length,error:v.error});if(v.rawGoal||v.base)captures.push(v)}
const before=fullWork(),start=performance.now(),results:any[]=[];let proof:any
counted(fullRate,()=>withWall(start+4800,()=>{const until=clock()+budget,attempt=countedAttempts(p.m,p.caller.map((i:number)=>p.laws[i]),new Set(p.support.map((i:number)=>p.laws[i])),until);attempt.houdini=true
 for(const pass of [0,1] as const){if(clock()>=until)break;const t=performance.now(),u=fullWork(),result=withDeadline(until,()=>attempt.traced(law,p.laws,pass,Math.max(0,until-clock())));results.push({pass,outcome:'proof'in result?'proof':result.stuck,units:(fullWork()-u)/fullRate,wallMs:performance.now()-t});if('proof'in result){proof=result.proof;break}}
}),true)
countsDump.on=undefined
const units=(fullWork()-before)/fullRate,wallMs=performance.now()-start,checked=!!proof&&countedObligations(p.m,p.laws,{[law.name]:proof.instances},index).every(({goal,decls})=>{const c=proof.certs[goal.name];return !!c&&checkMC(goal.hyps,decls,c)}),columns=[]
for(let i=0;;i++){const t=columnTerm(`⟦${i}⟧`);if(t===undefined)break;columns.push(t)}
const record={conditional:true,tag,law:law.name,familySize:p.laws.length,budget,wallAllowance:4800,units,wallMs,checked,results,profile:{...cprof},last:events.at(-1),events}
writeFileSync(join(out,'summary.json'),JSON.stringify(record,null,2)+'\n');writeFileSync(join(out,'capture.json.gz'),gzipSync(JSON.stringify({record,m:p.m,laws:p.laws,columns,captures,proof})));console.log(JSON.stringify(record))
