// Current-source replay of one captured op, not a complete-law certificate.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
import {columnTerm,countedObligations,termColumn} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
import {certFor} from '../../core/counts.ts'
import {focusCountCert} from '../../core/count-focused.ts'
import {proveCountCases} from '../../core/count-cases.ts'
import {checkConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {shardControl as s} from './section13-control.ts'
import {lemmaRecorder as ledger} from './section18-recorder.ts'
import {fieldAttemptObserver,type FieldAttempt} from '../../core/count-recovery/field-demand.ts'
import {pack} from './section18-codec.ts'
const [file,opText,out]=process.argv.slice(2),op=Number(opText),raw=readFileSync(file!,'utf8'),p=JSON.parse(raw),{m,laws,at,cert,context,options}=p,law=laws.find((l:any)=>l.name===p.lawName),index=laws.indexOf(law)
if(!law||!out||!Number.isInteger(op))throw Error('PACKET OP OUT required')
for(const [i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw Error('column restoration failed')
mkdirSync(out,{recursive:true});ledger.reset(m,law.name,op);s.mode='run';s.op=op;s.capture=()=>{}
let result:any,error:string|undefined;const done={},attempts:FieldAttempt[]=[],events:any[]=[];s.finish=r=>{result=r;throw done};fieldAttemptObserver.on=e=>attempts.push(e)
const start=performance.now(),work=fullWork(),allowance=5000,wallAllowance=4800
try{withWall(start+wallAllowance,()=>counted(fullRate,()=>proveCountCases(m,laws,at,cert,clock()+allowance,next=>{const g=countedObligations(m,laws,{[law.name]:next},index).find(x=>x.goal.name.endsWith('@step'));if(!g)throw Error('missing step');return g},{...options,trace:(e:any)=>events.push(e),propose:(g,ds)=>focusCountCert(m,ds,certFor(g,ds,true,1000),{carried:context.carried??undefined,structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,targets:context.targets,claim:g.hyps.at(-1)})}),true))}catch(e){if(e!==done)error=String(e)}finally{fieldAttemptObserver.on=undefined}
const searchUnits=(fullWork()-work)/fullRate,searchWallMs=performance.now()-start,checkStart=performance.now(),checkWork=fullWork(),checked=!!result&&checkConditionalProof(result.goal,result.tree,result.from??result.path),audit=ledger.audit()
const record={conditional:true,frozenActualFamily:true,units:(fullWork()-work)/fullRate,wallMs:performance.now()-start,checkWallMs:performance.now()-checkStart,checkUnits:(fullWork()-checkWork)/fullRate,law:law.name,op,packetSha256:createHash('sha256').update(raw).digest('hex'),allowance,wallAllowance,searchUnits,searchWallMs,checked,error,helperFrames:audit.frames,attempts,events}
const columns=[];for(let i=0;;i++){const term=columnTerm(`⟦${i}⟧`);if(term===undefined)break;columns.push(term)}
const proof=result?{goal:result.goal,tree:result.tree,path:[...(result.from??result.path)],marks:ledger.snapshots(result.tree)}:undefined
writeFileSync(join(out,'result.json'),pack({...record,columns,proof}))
console.log(JSON.stringify({...record,helperFrames:undefined,attempts:undefined,events:undefined,fieldUnits:audit.frames.filter(f=>f.name==='field').reduce((n,f)=>n+(f.exclusive??0),0),frameUnits:audit.frames.filter(f=>f.name==='frame').reduce((n,f)=>n+(f.exclusive??0),0),attemptCount:attempts.length,rowQueries:events.filter(e=>e.stage==='row-case'&&!e.cached).length,rowSplits:events.filter(e=>e.stage==='row-demand').length,rowMirrors:events.filter(e=>e.stage==='row-mirror').length,writeFreeCases:events.filter(e=>e.stage==='write-free-case').length,knownDemand:attempts.filter(a=>a.requested!==undefined).length,notDemandedUnits:attempts.filter(a=>a.requested===false).reduce((n,a)=>n+a.units,0)}))
