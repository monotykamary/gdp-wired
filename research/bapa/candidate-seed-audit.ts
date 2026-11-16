// Restatement only. This program intentionally never calls a prover.
import {createHash} from 'node:crypto'
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {resolve,join} from 'node:path'
import {pathToFileURL} from 'node:url'
import {installProfile} from './proof-worker.ts'
installProfile(process.env)
const {loadCandidateSeedManifest}=await import('./candidate-seed-manifest.ts')
const {workAdmissionSnapshot}=await import('../../core/work-admission.ts')
const {ghostedOk}=await import('../../kernel/kernel.ts')
const config=JSON.parse(readFileSync(process.argv[2]??'research/bapa/seed-audit-six.json','utf8')) as {id:string,models:string,manifest:string}[]
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR??'runs/seed-audit';mkdirSync(out,{recursive:true})
const sha=(x:string|Uint8Array)=>createHash('sha256').update(x).digest('hex')
const results:unknown[]=[]
for(const item of config){
 const {protocols}=await import(pathToFileURL(resolve(item.models)).href)
 const matches=protocols.filter((p:{id:string})=>p.id===item.id)
 if(matches.length!==1)throw Error(`expected one protocol ${item.id}`)
 const p=matches[0],r=p.make(),publicLaws=p.laws(r),machine=r.machine,before=JSON.stringify(machine)
 const counters=JSON.stringify(workAdmissionSnapshot().counters)
 const loaded=loadCandidateSeedManifest(item.manifest,machine,{kindLaws:r.kindLaws(),publicLaws})
 const ghostsQualified=loaded.kind==='usual'&&loaded.ghosts?ghostedOk({orig:machine,...loaded.ghosts}):undefined
 if(counters!==JSON.stringify(workAdmissionSnapshot().counters))throw Error(`${item.id}: restatement invoked native work`)
 if(before!==JSON.stringify(machine))throw Error(`${item.id}: restatement mutated supplied source`)
 const rematerialized=r.machine
 if(JSON.stringify(machine.sums??{})!==JSON.stringify(rematerialized.sums??{}))throw Error(`${item.id}: restatement added public sums`)
 const drops=loaded.audit.laws.filter(a=>a.status==='dropped')
 const result={protocol:item.id,noSearch:true,publicCalls:0,publicExistentialGoals:publicLaws.filter((l:{some?:string[]})=>l.some?.length).length,kind:loaded.kind,ghostsQualified,sourceUnchanged:true,rematerializationChanges:before!==JSON.stringify(rematerialized),modelsSha256:sha(readFileSync(item.models)),machineSha256:sha(before),proposed:loaded.laws.length,witnessProposals:loaded.audit.witnesses?.filter(w=>w.status==='proposed').length??0,witnessRefusals:loaded.audit.witnesses?.filter(w=>w.status==='dropped')??[],nativeKinds:loaded.audit.laws.filter(a=>a.status==='candidate'&&a.regeneratedKind).length,expandedKinds:loaded.audit.laws.filter(a=>a.status==='candidate'&&a.expandedKind).length,fieldRowProposals:loaded.audit.laws.filter(a=>a.status==='candidate'&&a.fieldRows).length,dropped:drops.length,drops,audit:loaded.audit}
 results.push(result);writeFileSync(join(out,`${item.id}.json`),JSON.stringify(result,null,2)+'\n')
 console.log(JSON.stringify({protocol:item.id,proposed:loaded.laws.length,dropped:drops.length,drops}))
}
writeFileSync(join(out,'seed-audit-six.json'),JSON.stringify({schema:'candidate-seed-restatement-six/v1',noSearch:true,publicCalls:0,results},null,2)+'\n')
