// One target law with the same bounded prefix warmup as the production family.
// Only the target's search deadlines are disabled. This is never a gate claim.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {type Law,type Machine} from '../../core/machine.ts'
import {certFor} from '../../core/counts.ts'
import {proveFocusedCounts} from '../../core/count-focus-proof.ts'
import {checkMC,columnTerm,countedObligations} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withTrees,withWall} from '../../kernel/prove.ts'
import {realNow,withoutDeadlines} from './without-deadlines.ts'
import {section12Recorder} from './section12-recorder.ts'
const [input,target,out]=process.argv.slice(2)
if(!input||!out||!['Inv*','Inv2973'].includes(target!))throw new Error('INPUT Inv*|Inv2973 OUT required')
const {m,laws}=JSON.parse(readFileSync(input,'utf8')) as {m:Machine,laws:Law[]},recorder=section12Recorder(join(out,'actions.jsonl'))
const selected=laws.filter(l=>['one primary','Inv3915','Inv1758','Inv2973','Inv*'].some(p=>l.name.startsWith(p)))
const check=(law:Law,proof:ReturnType<typeof proveFocusedCounts>)=>!!proof&&countedObligations(m,laws,{[law.name]:proof.instances},laws.indexOf(law)).every(p=>!!proof.certs[p.goal.name]&&checkMC(p.goal.hyps,p.decls,proof.certs[p.goal.name]!))
withTrees(()=>{
 for(const law of selected){
  const active=law.name.startsWith(target!),start=realNow(),before=fullWork();recorder.reset(law.name)
  const search=()=>proveFocusedCounts(m,laws,law,{},clock()+5000,(goal,decls)=>certFor(goal,decls,true,1000),()=>{})
  if(!active){const result=withWall(performance.now()+60000,()=>counted(fullRate,()=>{const proof=search();return {proven:!!proof,checked:check(law,proof)}},true));console.log(JSON.stringify({warmup:law.name,...result,units:(fullWork()-before)/fullRate,wallMs:realNow()-start}));continue}
  console.log(JSON.stringify({event:'unlimited-start',law:law.name,productionAllowance:5000,deadlines:'disabled',structuralLimits:'unchanged'}))
  const proof=withoutDeadlines(search),searchUnits=(fullWork()-before)/fullRate,searchWallMs=realNow()-start,checkStart=realNow(),checked=check(law,proof),checkWallMs=realNow()-checkStart,totalUnits=(fullWork()-before)/fullRate,wallMs=realNow()-start
  const columns=[];for(let i=0;;i++){const t=columnTerm(`⟦${i}⟧`);if(t===undefined)break;columns.push(t)}
  const data={revision:'5974b9165d6860f1157f3bed3cd66a7e1514e904',researchOnly:true,law:law.name,proven:!!proof,checked,searchUnits,totalUnits,searchWallMs,checkWallMs,wallMs,productionAllowance:5000,ratioToProductionAllowance:totalUnits/5000,...recorder.result(totalUnits),columns}
  writeFileSync(join(out,'result.json'),JSON.stringify(data)+'\n')
  if(proof)writeFileSync(join(out,'proof.json'),JSON.stringify({law:law.name,proof,columns})+'\n')
  console.log(JSON.stringify({event:'unlimited-result',law:law.name,proven:!!proof,checked,totalUnits,wallMs,ledger:data.ledger,outsideActions:data.outsideActions,firstFailure:data.firstFailure&&{kind:data.firstFailure.kind,reason:data.firstFailure.reason,action:data.firstFailure.action,path:data.firstFailure.path,model:data.firstFailure.capture?.model,violated:data.firstFailure.capture?.violated},finalUnresolved:data.finalUnresolved}))
  break
 }
})
