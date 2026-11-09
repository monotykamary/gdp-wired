// One research-only original-family helper x operation x counted-pass shard.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
import {all,same,x,n,type Law,type Machine} from '../../../core/machine.ts'
import {countedAttempts,countsDump} from '../../../core/counts.ts'
import {finiteCountChoice} from '../../../core/count-cases.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../../kernel/prove.ts'
import {checkMC,countedObligations,columnTerm} from '../../../kernel/kernel.ts'
import {upperControl} from './control.ts'
const [file,tag,opText,passText,ceilings,wallText='1800000']=process.argv.slice(2),bytes=readFileSync(file!),p=JSON.parse(bytes.toString()),op=Number(opText),pass=Number(passText),wallMs=Number(wallText),budget=1e12
if(!p.originalHarness||!p.generatorOnly||p.suppliedLaws.length||p.laws.length!==34||!(pass===0||pass===1)||!(ceilings==='on'||ceilings==='off')||!(wallMs>0&&wallMs<=1800000))throw Error('invalid upper-bound shard contract')
const choice=finiteCountChoice(p.m);if(!choice||!choice[1].has(op))throw Error('operation not present in original machine')
const law:Law=p.laws[p.targets[tag!]];if(!law)throw Error('missing target')
const m:Machine={...p.m,assume:all(...(p.m.assume?[p.m.assume]:[]),same(x(choice[0]),n(op)))}
const familyHash=createHash('sha256').update(bytes).digest('hex'),meta={researchOnly:true,originalFamily:true,sourceSha:p.sourceSha,familyHash,law:law.name,tag,operation:{name:choice[0],value:op},pass,ceilings,noShare:true,countedBudget:budget,wallLimitMs:wallMs,familySize:p.laws.length,suppliedLaws:[],conditional:'original STEP under operation equality',cpu:readFileSync('/proc/cpuinfo','utf8').split('\n').find(l=>l.startsWith('model name'))}
mkdirSync('upper-output',{recursive:true});upperControl.start(meta);countsDump.on=e=>upperControl.event(e)
const start=performance.now(),before=fullWork();let result:ReturnType<ReturnType<typeof countedAttempts>['traced']>|undefined,error:string|undefined,proof:any
try{counted(fullRate,()=>withWall(start+wallMs,()=>{const until=clock()+budget,attempt=countedAttempts(m,p.caller.map((i:number)=>p.laws[i]),new Set(p.support.map((i:number)=>p.laws[i])),until);attempt.houdini=true;result=attempt.traced(law,p.laws,pass,budget);if('proof'in result)proof=result.proof}),true)}catch(e){error=String(e)}finally{countsDump.on=undefined}
const searchWallMs=performance.now()-start,searchUnits=(fullWork()-before)/fullRate,progress=upperControl.finish();let checked=false,checkError:string|undefined
try{checked=!!proof&&countedObligations(m,p.laws,{[law.name]:proof.instances},p.targets[tag!]).filter(({goal})=>goal.name.endsWith('@step')).every(({goal,decls})=>!!proof.certs[goal.name]&&checkMC(goal.hyps,decls,proof.certs[goal.name]))}catch(e){checkError=String(e)}
const status=checked?'closed':searchWallMs>=wallMs-20?'censored':result&&'stuck'in result&&result.stuck==='sat'&&result.refuted?'sat':'unknown'
const record={...meta,status,checked,freshProcessCheckPending:checked,searchUnits,searchWallMs,countedUnits:(fullWork()-before)/fullRate,wallMs:performance.now()-start,peakRssKiB:process.resourceUsage().maxRSS,result:result&&'stuck'in result?{stuck:result.stuck,refuted:result.refuted}:undefined,error,checkError,progress}
writeFileSync('upper-output/result.json',JSON.stringify(record));console.log('UPPER_RESULT '+JSON.stringify(record))
if(checked){const columns=[];for(let i=0;;i++){const term=columnTerm(`⟦${i}⟧`);if(term===undefined)break;columns.push(term)}writeFileSync('upper-output/proof.json.gz',gzipSync(JSON.stringify({meta,m,laws:p.laws,index:p.targets[tag!],proof,columns})))}
