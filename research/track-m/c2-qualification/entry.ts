import {closeSync,openSync,readFileSync,writeFileSync,writeSync} from 'node:fs'
import type {Manifest,MeterBinding} from './contract.ts'
import {assertManifest,digest} from './assertions.ts'
export async function main(gate:'closure'|'half'|'both'):Promise<void>{
 const file=process.argv[2],output=process.argv[3],execute=process.argv.includes('--execute')
 if(!file){console.log(JSON.stringify({gate,status:'NOT_RUN',reason:'prepare-only: supply a sealed manifest; execution also requires explicit --execute and a GO release binding'}));return}
 const manifest=JSON.parse(readFileSync(file,'utf8')) as Manifest
 try{assertManifest(manifest)}catch(e){console.log(JSON.stringify({gate,status:'NOT_RUN',reason:'unbound manifest: '+String(e)}));if(execute)process.exitCode=2;return}
 if(!execute||manifest.authorization.status!=='GO'||!manifest.authorization.releaseSha256?.match(/^[0-9a-f]{64}$/)){
  console.log(JSON.stringify({gate,status:'NOT_RUN',manifestSha256:digest(manifest),reason:'prepare-only or missing exact qualification release'}));return
 }
 if(!output)throw Error('an output receipt path is required')
 // Clear inheritance BEFORE any production/meter module is loaded.
 for(const key of Object.keys(process.env))if(key.startsWith('GDP_'))delete process.env[key]
 Object.assign(process.env,manifest.flags)
 const path=new URL('../../../core/work-admission.ts',import.meta.url).href
 let meter:MeterBinding
 try{const mod=await import(path) as Partial<MeterBinding>;if(typeof mod.workLedger?.withBudget!=='function'||typeof mod.workAdmissionSnapshot!=='function'||typeof mod.withWorkAdmissionTrace!=='function')throw Error('missing T309 exports');meter=mod as MeterBinding}
 catch(e){const receipt={gate,status:'NOT_RUN',reason:'T309 lease binding absent: '+String(e),manifestSha256:digest(manifest)};writeFileSync(output,JSON.stringify(receipt,null,2)+'\n');console.log(JSON.stringify(receipt));process.exitCode=2;return}
 const {runProductionQualification}=await import('./production.ts'),tracePath=output+'.lease-events.jsonl',fd=openSync(tracePath,'wx')
 let receipt:Awaited<ReturnType<typeof runProductionQualification>>
 try{receipt=await runProductionQualification(manifest,meter,event=>{const line=JSON.stringify(event)+'\n',bytes=Buffer.from(line);let offset=0;while(offset<bytes.length){const wrote=writeSync(fd,bytes,offset,bytes.length-offset);if(wrote<=0)throw Error('trace write made no progress');offset+=wrote}})}finally{closeSync(fd)}
 const {payload,...metadata}=receipt
 if(payload)writeFileSync(output+'.family.json',JSON.stringify(payload)+'\n')
 writeFileSync(output,JSON.stringify({...metadata,familyArtifact:payload?output+'.family.json':null,traceArtifact:tracePath},null,2)+'\n')
 console.log(JSON.stringify({gate,closure:receipt.closure,half:receipt.half,prefix:receipt.prefix,manifestSha256:receipt.manifestSha256}))
 const selected=gate==='closure'?[receipt.closure]:gate==='half'?[receipt.half]:[receipt.closure,receipt.half]
 if(selected.some(v=>v.status!=='PASS'))process.exitCode=1
}
