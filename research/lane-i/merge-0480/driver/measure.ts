import {createHash} from 'node:crypto'
import {readFileSync,realpathSync,writeFileSync} from 'node:fs'
import {resolve,join} from 'node:path'
import {gzipSync} from 'node:zlib'
const [root,id,unitsText,output,source,target]=process.argv.slice(2), allowance=Number(unitsText)
if(!root||!id||!output||!source||!target||!Number.isFinite(allowance)||allowance<0)throw Error('invalid measurement arguments')
const custody=Object.fromEntries(['kernel/kernel.ts','core/check.ts'].map(path=>{const resolved=realpathSync(Bun.resolveSync(join(root,path),root));if(resolved!==join(realpathSync(root),path))throw Error('unexpected checker resolution');return[path,createHash('sha256').update(readFileSync(resolved)).digest('hex')]}))
const {proveRule}=await import(join(root,'core/dsl.ts'))
const {protocols}=await import(join(root,'research/protocols/ic3syn/models.ts'))
const {countsDump}=await import(join(root,'core/counts.ts'))
const {rawWork,fullWork,workKeys,completeWorkWeights}=await import(join(root,'core/work-meter.ts'))
const {withWorkLedger,workPhase}=await import(join(root,'core/work-ledger.ts'))
const {queryHook}=await import(join(root,'kernel/prove.ts'))
const protocol=protocols.find((p:any)=>p.id===id)
if(!protocol)throw Error('unknown original model '+id)
const phases:any[]=[],events:any[]=[],queries:any[]=[]
const started=fullWork(),rawStart=rawWork()
let searchStart=started,searchEnd=started,searchRawStart=rawStart,searchRawEnd=rawStart,generated:any
function compact(event:any){const out:any={};for(const [key,value]of Object.entries(event)){if(['machine','laws','rawGoal','decls','certificateRequest','goal','witness','path','hyps'].includes(key))continue;if(value===null||['string','number','boolean'].includes(typeof value))out[key]=value;else if(Array.isArray(value)&&value.every(v=>v===null||['string','number','boolean'].includes(typeof v)))out[key]=value}if(typeof event.goal==='string')out.goal=event.goal;else if(event.goal?.name)out.goal=event.goal.name;return out}
countsDump.on=(event:any)=>{if(event.phase==='candidates')generated={count:event.laws.length,hash:createHash('sha256').update(JSON.stringify(event.laws)).digest('hex'),laws:event.laws.map((l:any)=>l.name)};events.push({...compact(event),atUnits:fullWork()-started,raw:rawWork()})}
queryHook.on=(query:any)=>queries.push({kind:query.kind,goal:query.goal?.name,depth:query.depth,status:'tree'in query.out?'proposed':query.out.stuck,why:query.out.why,nodes:query.out.nodes,atUnits:fullWork()-started})
const clockGate=(globalThis as unknown as {commonCensusClock?:{active:boolean,reads:number}}).commonCensusClock
if(clockGate)clockGate.active=true
let result:any,error:any,lawNames:string[]=[]
withWorkLedger('original:'+id,(phase:any)=>phases.push(phase),()=>{
 try{const rule=workPhase('protocol.construct',()=>protocol.make()),laws=workPhase('protocol.laws',()=>protocol.laws(rule));lawNames=laws.map((l:any)=>l.name);searchStart=fullWork();searchRawStart=rawWork();try{result=workPhase('rule.prove',()=>proveRule(rule,laws,{search:{work:allowance}}))}finally{searchEnd=fullWork();searchRawEnd=rawWork()}}
 catch(e){error={name:(e as Error).name,message:(e as Error).message,stack:(e as Error).stack}}
})
if(clockGate)clockGate.active=false
const delta=(a:any,b:any)=>Object.fromEntries(workKeys.map((k:string)=>[k,a[k]-b[k]]))
const verdict=error?'error':result?.proven&&result?.checked?'proven':result?.run?'refuted':'unknown'
const brief={verdict,proven:!!result?.proven,checked:!!result?.checked,goal:result?.goal,stuck:result?.stuck,why:result?.why,failed:result?.failed,found:result?.found?.laws?.map((l:any)=>l.source??l.text),error}
const receipt={custody,schema:'lane-i-candidate-v1',status:'COUNTED-PORT-PENDING-D',source,target,id,variant:'original',allowance,unitStatus:'UNCALIBRATED',clockReads:clockGate?.reads,weights:completeWorkWeights(),knobs:Object.fromEntries(Object.entries(process.env).filter(([key])=>key.startsWith('GDP_'))),laws:lawNames,result:brief,units:fullWork()-started,searchUnits:searchEnd-searchStart,raw:delta(rawWork(),rawStart),searchRaw:delta(searchRawEnd,searchRawStart),generated,phases,events,queries}
writeFileSync(resolve(output),gzipSync(JSON.stringify(receipt)))
console.log('MEASURE_DONE '+JSON.stringify({id,source,target,allowance,result:brief,searchUnits:receipt.searchUnits,phaseCount:phases.length,eventCount:events.length,queryCount:queries.length,generated}))
