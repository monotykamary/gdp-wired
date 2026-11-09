// A per-law cost diagnostic, not an accepted jointly checked family.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {gzipSync} from 'node:zlib'
import {certFor,countedAttempts,countsDump,cprof} from '../../core/counts.ts'
import {focusedCountRecoveryEnabled,proveFocusedCounts} from '../../core/count-focus-proof.ts'
import {walkOnce} from '../../core/machine.ts'
import {clock,counted,fullRate,fullWork,withDeadline,withWall} from '../../kernel/prove.ts'
import {checkMC,columnTerm,countedObligations} from '../../kernel/kernel.ts'
import {conditionalProofStats} from '../../core/count-recovery/conditional-proof.ts'
import {readCheckProfile} from './check-cost-profile.ts'
const [input,tag,out,budgetArg='2700',wallArg='4800']=process.argv.slice(2),p=JSON.parse(readFileSync(input!,'utf8')),index=p.targets[tag!],law=p.laws[index],budget=Number(budgetArg),wallAllowance=Number(wallArg)
const section16=budget===6000&&wallAllowance===7000&&p.generatorOnly===true&&(p.suppliedLaws?.length??0)===0
const order=process.env.LANE_B_PASS_ORDER??'ordinary-first';if(!['ordinary-first','count-first'].includes(order))throw Error('invalid LANE_B_PASS_ORDER')
const passOrder:(0|1)[]=order==='count-first'?[1,0]:[0,1]
const earlyFocusMode=process.env.LANE_B_EARLY_FOCUS??'off';if(!['off','third','only'].includes(earlyFocusMode))throw Error('invalid LANE_B_EARLY_FOCUS')
let readsCount=false;walkOnce(law?.holds,(v:any)=>{if(v.op==='get'&&p.m.counts?.[v.map])readsCount=true})
const earlyEligible=!!law?.keys?.length&&!readsCount&&focusedCountRecoveryEnabled(p.m)
if(!law||!out||!((budget>0&&budget<=5000&&wallAllowance===4800)||section16))throw Error('FAMILY TARGET OUTPUT [budget <=5000] [4800], or actual generated family with 6000 7000')
mkdirSync(out,{recursive:true});const events:any[]=[],captures:any[]=[]
countsDump.on=e=>{const v=e as any;events.push({phase:v.phase,pass:v.pass,goal:v.goal,law:v.law,hyps:v.hyps?.length,error:v.error,added:v.added});if(v.rawGoal||v.base)captures.push(v)}
const before=fullWork(),cacheBefore=conditionalProofStats(),start=performance.now(),results:any[]=[];let proof:any
counted(fullRate,()=>withWall(start+wallAllowance,()=>{const until=clock()+budget,attempt=countedAttempts(p.m,p.caller.map((i:number)=>p.laws[i]),new Set(p.support.map((i:number)=>p.laws[i])),until);attempt.houdini=true
 if(earlyFocusMode!=='off'&&earlyEligible){const t=performance.now(),u=fullWork(),focusUntil=earlyFocusMode==='only'?until:Math.min(until,clock()+budget/3),result=withDeadline(focusUntil,()=>proveFocusedCounts(p.m,p.laws,law,{},focusUntil,(g,ds)=>certFor(g,ds,true,Number(process.env.GDP_COUNTS_POOL??1000)),e=>events.push({phase:'early-focus',...e})));results.push({pass:'early-focus',outcome:result?'proof':'unknown',units:(fullWork()-u)/fullRate,wallMs:performance.now()-t});if(result)proof=result}
 for(const pass of passOrder){if(proof||earlyFocusMode==='only'&&earlyEligible||clock()>=until)break;const t=performance.now(),u=fullWork(),result=withDeadline(until,()=>attempt.traced(law,p.laws,pass,Math.max(0,until-clock())));results.push({pass,outcome:'proof'in result?'proof':result.stuck,units:(fullWork()-u)/fullRate,wallMs:performance.now()-t});if('proof'in result){proof=result.proof;break}}
}),true)
countsDump.on=undefined
const searchUnits=(fullWork()-before)/fullRate,searchWallMs=performance.now()-start,checkStart=performance.now(),checked=!!proof&&countedObligations(p.m,p.laws,{[law.name]:proof.instances},index).every(({goal,decls})=>{const c=proof.certs[goal.name];return !!c&&checkMC(goal.hyps,decls,c)}),columns=[]
for(let i=0;;i++){const t=columnTerm(`⟦${i}⟧`);if(t===undefined)break;columns.push(t)}
const units=(fullWork()-before)/fullRate,checkUnits=units-searchUnits,wallMs=performance.now()-start,checkWallMs=performance.now()-checkStart,cacheAfter=conditionalProofStats(),cache=Object.fromEntries(Object.entries(cacheAfter).map(([k,v])=>[k,v-cacheBefore[k as keyof typeof cacheBefore]]))
const record={conditional:true,standalone:true,passOrder,earlyFocusMode,earlyEligible,measurementVersion:4,diagnostic:section16?'section16.5':'legacy',generatorOnly:p.generatorOnly??false,familySource:p.source,suppliedLaws:p.suppliedLaws??[],tag,law:law.name,familySize:p.laws.length,budget,wallAllowance,units,searchUnits,checkUnits,searchWallMs,checkWallMs,wallMs,checked,withinDiagnosticLine:section16&&checked&&units<=6000&&wallMs<=7000,cache,checkProfile:readCheckProfile(),results,profile:{...cprof},last:events.at(-1),events}
writeFileSync(join(out,'summary.json'),JSON.stringify(record,null,2)+'\n');writeFileSync(join(out,'capture.json.gz'),gzipSync(JSON.stringify({record,m:p.m,laws:p.laws,columns,captures,proof})));console.log(JSON.stringify(record))
