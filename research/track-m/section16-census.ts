// Receipt-only census. No prover imports, proof rerun or new policy.
import {readFileSync,readdirSync,statSync,writeFileSync,mkdtempSync} from 'node:fs'
import {join,relative} from 'node:path'
import {homedir} from 'node:os'
import {createHash} from 'node:crypto'
import {brotliDecompressSync} from 'node:zlib'
import {statement} from './section16-statements.ts'
const root=process.argv[2];if(!root)throw new Error('ROOT required')
const files=(p:string):string[]=>readdirSync(p).flatMap(n=>{const q=join(p,n);return statSync(q).isDirectory()?files(q):[q]})
const target=new Set(['field-bound','frame-lemma','count-lemma','read-alias','field-domain','field-bound-conclusion','frame-conclusion'])
const inventory:any[]=[],events:any[]=[],profiles:any[]=[]
const digest=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
const parse=(text:string):any[]=>{try{return [JSON.parse(text)]}catch{return text.split('\n').flatMap(l=>{if(!l.startsWith('{'))return [];try{return [JSON.parse(l)]}catch{return []}})}}
const inspect=(name:string,text:string,receipt:string)=>{
 const records=parse(text);if(!records.length)return
 const counts:Record<string,number>={},samples:any[]=[],stages:Record<string,number>={}
 for(const record of records){
  const stack:{o:any,context:any,path:string}[]=[{o:record,context:{law:record.law,op:typeof record.op==='number'?record.op:typeof record.value==='number'?record.value:undefined},path:'$'}]
  while(stack.length){const {o,context,path}=stack.pop()!;if(!o||typeof o!=='object')continue
   const ctx={...context};if(typeof o.law==='string')ctx.law=o.law;if(typeof o.op==='number')ctx.op=o.op;if((o.diagnostic||typeof o.stage==='string')&&typeof o.value==='number')ctx.op=o.value
   if(o.cert?.reads&&o.cert?.insts)ctx.cert=o.cert
   if(o.reads&&Array.isArray(o.insts))ctx.cert={reads:o.reads,insts:o.insts}
   if(o.trace?.frames&&typeof o.units==='number')profiles.push({file:name,receipt,law:ctx.law,op:ctx.op,units:o.units,sites:o.sites??[],helperEvents:o.trace.events.filter((e:any)=>target.has(e.stage??e.kind)).length,frameKinds:[...new Set(o.trace.frames.map((f:any)=>f.kind))],traceKeys:Object.keys(o.trace)})
   if(typeof o.stage==='string'){stages[o.stage]=(stages[o.stage]??0)+1;if(target.has(o.stage)){
    const good=o.proved===true||o.checked===true||o.proposed===true,cert=ctx.cert,inst=cert?.insts?.[o.index]
    const event={file:name,receipt,path,law:ctx.law,op:ctx.op,...o,inst,reads:inst?.terms?.map((t:any)=>cert.reads.find((r:any)=>r[0]===t[1]))}
    if(good)events.push(event);counts[o.stage]=(counts[o.stage]??0)+1;if(samples.length<2)samples.push(event)
   }}
   for(const [key,value]of Object.entries(o))if(!['m','model','witness','tree','numeric','cert','reads','insts','columns','hyps','counts','decls','source','proofSource','delta','frames','captures','available'].includes(key)&&value&&typeof value==='object')stack.push({o:value,context:ctx,path:path+'.'+key})
  }
 }
 if(Object.keys(counts).length)inventory.push({file:name,receipt,counts,stages,samples})
}
const archives:any[]=[],failures:any[]=[]
for(const f of files(root).sort()){
 const name=relative(root,f);if(name.endsWith('.br')){
  const bytes=readFileSync(f),sha=digest(bytes),manifest=join(f.slice(0,f.lastIndexOf('/')),'archive-manifest.json');let verified=false
  try{const m=JSON.parse(readFileSync(manifest,'utf8'));if(m.sha256!==sha)throw new Error('hash mismatch');verified=true}catch(e){if(String(e).includes('hash mismatch'))throw e}
  try{const packed=JSON.parse(brotliDecompressSync(bytes).toString()),names=Object.keys(packed);archives.push({file:name,sha256:sha,verified,files:names});for(const [file,text]of Object.entries(packed))if(typeof text==='string'&&!/\.(js|ts)$/.test(file))inspect(name+'!'+file,text,sha)}catch(e){failures.push({file:name,error:String(e)})}
 }else if(name.endsWith('.log'))inspect(name,readFileSync(f,'utf8'),digest(readFileSync(f)))
}
const out=mkdtempSync(join(homedir(),'track-m-section16-'));const result={receiptOnly:true,archives,failures,inventory,positiveEvents:events,profiles}
const catalog=events.map(e=>({file:e.file,receipt:e.receipt,path:e.path,law:e.law??null,op:e.op??null,stage:e.stage,statement:statement(e),checked:e.checked===true,reportedProved:e.proved===true,proposed:e.proposed===true,deferred:e.deferred===true,recordedClockDelta:e.ms??null,individualCountedUnits:null,rootScopeAvailable:false}))
const normalized=new Map<string,any>();for(const row of catalog)if(row.statement){const key=row.statement.text;let group=normalized.get(key);if(!group){group={...row.statement,occurrences:[]};normalized.set(key,group)}group.occurrences.push(row)}
writeFileSync(join(out,'lemma-catalog.json'),JSON.stringify({receiptOnly:true,warning:'Positive event records are not necessarily checked lemmas. Historical clock deltas are not attributed to T-12. A guard-free statement is not a proof of root validity.',normalized:[...normalized.values()],unresolved:catalog.filter(r=>!r.statement)},null,2)+'\n')
writeFileSync(join(out,'census.json'),JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify({output:out,archives:archives.length,positiveEvents:events.length,inventory:inventory.length,failures,profiles:profiles.filter(p=>p.file.includes('section15-t12-v3')).map(p=>({file:p.file,op:p.op,helperEvents:p.helperEvents,frameKinds:p.frameKinds}))}))
const p=Bun.spawn(['bun','research/track-m/pack-section10-archive.ts',join(out,'census.json'),join(out,'lemma-catalog.json')],{stdout:'inherit',stderr:'inherit'});if(await p.exited)throw new Error('packing failed')
