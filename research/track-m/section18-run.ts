import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {countedObligations,termColumn,columnTerm} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
import {certFor} from '../../core/counts.ts'
import {focusCountCert} from '../../core/count-focused.ts'
import {proveCountCases} from '../../core/count-cases.ts'
import {checkConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {shardControl as s} from './section13-control.ts'
import {lemmaRecorder as r} from './section18-recorder.ts'
import {pack} from './section18-codec.ts'
const [file,opText,out,mode='observe']=process.argv.slice(2),op=Number(opText);if(!file||!out||!Number.isInteger(op))throw Error('PACKET OP OUT [observe|control]')
const p=JSON.parse(readFileSync(file,'utf8')),{m,laws,at,cert,packet,context,options}=p,law=laws.find((l:any)=>packet.goal.name.startsWith(l.name)),index=laws.indexOf(law)
for(const [i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw Error('column restoration failed')
mkdirSync(out,{recursive:true});r.reset(m,law.name,op,mode==='observe');s.mode='run';s.op=op;s.capture=()=>{};let result:any;const done={};s.finish=x=>{result=x;throw done}
const start=performance.now(),work=fullWork(),allowance=5000,wallAllowance=4800,events:any[]=[];let error:string|undefined
try{withWall(start+wallAllowance,()=>counted(fullRate,()=>proveCountCases(m,laws,at,cert,clock()+allowance,next=>{const g=countedObligations(m,laws,{[law.name]:next},index).find(x=>x.goal.name.endsWith('@step'));if(!g)throw Error('missing step');return g},{...options,trace:(e:any)=>events.push(e),propose:(g,ds)=>focusCountCert(m,ds,certFor(g,ds,true,1000),{carried:context.carried??undefined,structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,targets:context.targets,claim:g.hyps.at(-1)})}),true))}catch(e){if(e!==done)error=String(e)}
const searchUnits=(fullWork()-work)/fullRate,searchWallMs=performance.now()-start,auditStart=performance.now(),checked=!!result&&checkConditionalProof(result.goal,result.tree,result.from??result.path),audit=r.audit()
const output={...audit,researchOnly:true,engine:p.revision,law:law.name,op,mode,allowance,wallAllowance,productionLocalCeilings:true,t12:false,closed:checked,verdict:checked?'closed':'unknown',searchUnits,searchWallMs,auditWallMs:performance.now()-auditStart,error,events}
Object.assign(output,{root:r.roots[0],stateFields:Object.keys(m.state)})
const columns=[];for(let i=0;;i++){const term=columnTerm(`⟦${i}⟧`);if(term===undefined)break;columns.push(term)}
writeFileSync(join(out,'result.json'),pack({...output,columns}));console.log(JSON.stringify({...output,frames:undefined,results:output.results.map(x=>({id:x.id,kind:x.kind,sourceChecked:x.sourceChecked,targetChecked:x.targetChecked,eligible:x.eligible,units:x.units})),events:undefined}))
if(error)process.exitCode=1
