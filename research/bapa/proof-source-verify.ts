// Verify a completed external Lean build against the exact emitted source files.
// This does not run Lean and must not replace the build step in the recipe.
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync} from 'node:fs'
import {resolve,sep,join} from 'node:path'
import {answers,gate} from '../../scripts/lean-gate/gate.ts'
const sha=(text:string)=>createHash('sha256').update(text).digest('hex')
export function verifyCountedSourceProject(directory:string,log:string){
 const root=resolve(directory),raw=readFileSync(join(root,'EMITTED.json'),'utf8'),r=JSON.parse(raw)
 if(r.schema!=='bapa-emission/v1'||r.status!=='EMITTED_NOT_CHECKED'||r.sourceProjection?.kind!=='counted'||r.leanExecuted!==false||r.allSizesProven!==false)throw Error('not an unverified counted source emission')
 if(!/^[a-f0-9]{64}$/.test(r.inputSha256)||!r.files||typeof r.files!=='object')throw Error('invalid input/file manifest')
 for(const [name,digest]of Object.entries(r.files)){
  const file=resolve(root,name)
  if(!file.startsWith(root+sep)||!/^([a-f0-9]{64})$/.test(String(digest))||sha(readFileSync(file,'utf8'))!==digest)throw Error('emitted file changed: '+name)
 }
 if(!r.files['BapaProof.lean']||!r.files['CountedSourceBridge.lean'])throw Error('required source files missing from manifest')
 const wanted:unknown[]=[r.familyTheorem,...(r.sourceProjection.sourceTheorems??[])]
 if(wanted.length<2||wanted.some(x=>typeof x!=='string'||!/^bapa_[A-Za-z0-9_]+$/.test(x))||new Set(wanted).size!==wanted.length)throw Error('invalid source theorem manifest')
 const errors=gate(log,[readFileSync(join(root,'BapaProof.lean'),'utf8')],false)
 if(errors.length)throw Error(errors.join('; '))
 const found=new Set(answers(log).map(x=>x.name))
 for(const name of wanted)if(!found.has(name as string))throw Error('missing exact theorem axiom output: '+name)
 if(!log.includes('Build completed successfully')||/\berror:/.test(log))throw Error('no clean completed Lean build in log')
 return {schema:'bapa-source-check/v1',status:'SOURCE_CHECKED',inputSha256:r.inputSha256,emissionSha256:sha(raw),leanLogSha256:sha(log),identity:r.identity,sourceProjection:r.sourceProjection,checkedTheorems:wanted,files:r.files,leanVersion:r.leanVersion}
}
if(import.meta.main){
 const [directory,logfile,out]=process.argv.slice(2)
 if(!directory||!logfile||!out)throw Error('usage: proof-source-verify.ts PROJECT LEAN_LOG NEW_RECEIPT')
 const result=verifyCountedSourceProject(directory,readFileSync(logfile,'utf8'))
 writeFileSync(out,JSON.stringify(result,null,2)+'\n',{flag:'wx'})
 console.log(JSON.stringify(result))
}
