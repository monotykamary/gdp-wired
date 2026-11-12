// Synthetic boundary controls only. No scheduler, candidate, proof or real custody claim.
import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {bindNativeReceipts,nativeCloseJson} from './receipt-bindings.ts'
import {replayDiagnosticCollector} from './replay-diagnostic.ts'
const root=mkdtempSync(join(tmpdir(),'s51-native-binding-'))
const hash=(bytes:string|Uint8Array)=>createHash('sha256').update(bytes).digest('hex')
const json=(path:string,value:unknown)=>writeFileSync(path,JSON.stringify(value)+'\n')
const name='mldr-3g-timed',batch='synthetic-binder-boundary',cpu='SYNTHETIC CPU, not a host observation'
function resources(phase:string):any{
 const limit={raw:'unlimited unlimited bytes',soft:'unlimited',hard:'unlimited',units:'bytes'}
 return {format:'mldr-3g-resource-observation/v1',phase,mode:'timed',workerPid:10,valid:true,observationOnly:true,collectorInvokedCandidateCode:false,platform:'linux',pidNamespace:{status:'OBSERVED',value:'pid:[100]'},affinity:{status:'OBSERVED',value:{count:16,cpuIds:Array.from({length:16},(_,i)=>i)}},memory:{requestedMiB:28672,requestedMeaning:'scheduler placement request, not an observed hard cap',perJobEnforcement:false,rlimits:{status:'OBSERVED',value:{addressSpace:limit,dataSize:limit,residentSet:limit}},cgroup:{status:'OBSERVED',value:{version:2,outsideVisibleMount:'UNKNOWN',limits:[{path:'/sys/fs/cgroup/memory.max',raw:'max'}]}}}}
}
try{
 const dir=join(root,name+'.files'),payloads=join(root,'.payloads'),custody=join(root,'custody')
 for(const path of [dir,payloads,custody])mkdirSync(path)
 const required=['verdict.json','identity.json','root-initial.json','root-final-before-unwind.json','root-settled.json','source-before.json','source-postinstall.json','source-after.json','resources-before.json','resources-after.json','resource-exits.json','worker-cleanup.json','ARTIFACTS.sha256','measurement-total.json','replay-declines.json','CONFIG.json','SEAL.json','INPUTS.sha256','AUTHORIZATION.json']
 for(const path of required)json(join(dir,path),{})
 const identity={sourceCommit:'synthetic-source',sourceTree:'synthetic-tree',mode:'timed'}
 json(join(dir,'verdict.json'),{synthetic:true,scope:'binder only, not a proof verdict',identity,mode:'timed'})
 json(join(dir,'replay-declines.json'),replayDiagnosticCollector({...identity,sealSHA256:hash(readFileSync(join(dir,'SEAL.json'))),inputIndexSHA256:hash(readFileSync(join(dir,'INPUTS.sha256')))}).finish())
 json(join(dir,'resources-before.json'),resources('before'));json(join(dir,'resources-after.json'),resources('after'))
 json(join(dir,'resource-exits.json'),{before:0,after:0});json(join(dir,'worker-cleanup.json'),{scratchRemoved:true,exitCode:0,workerPid:10})
 writeFileSync(join(dir,'cpu-model.txt'),cpu+'\n')
 const entries=[...required,'cpu-model.txt'].map(path=>{const bytes=readFileSync(join(dir,path));return {path,version:1,format:'file',sha256:hash(bytes),bytes:bytes.length}})
 const manifest=join(payloads,'manifest.json');json(manifest,entries);const manifestBytes=readFileSync(manifest)
 const attempt={name,run_name:name,vm:'synthetic-vm',boot_id:'synthetic-boot',launch_identity:'synthetic-launch',attempt:1,cleanup_complete:true}
 const close={batch,ok:true,complete:true,cleanup_complete:true,admission_closed:true,journals_retained:true,strict_once:true,max_attempts:1,pending:[],unlaunched:[],attempts:[attempt]}
 const events=[{sequence:1,event:'close_receipt',cleanup_complete:true,receipt_sha256:hash(nativeCloseJson(close))}]
 const journal=JSON.stringify(events[0])+'\n',journalHash=hash(journal);writeFileSync(join(custody,batch+'.jsonl'),journal)
 const bun={version:'1.4.3',sha256:'7ce7d6b654eddeec20afddf2396317fba6dc19ab52788a27e894e1806bf8f24b'}
 const row:any={...attempt,batch,status:'SUCCEEDED',code:0,terminal:true,identity_unavailable:false,strict_once:true,max_attempts:1,attempts:1,
  placement:{vm:attempt.vm,boot_id:attempt.boot_id,attempt:1,type:'xlarge',cpu,vcpus:16,exclusive:true,co_tenants:0},
  runtime_verified:true,runtime_verification:{protocol:1,ok:true,required:{bun},observed:{bun:{...bun,hash_matches:true,version_matches:true,stable:true}}},
  custody:{batch,max_attempts:1,sha256:journalHash,event_count:events.length,events},
  output_files_dir:dir,output_files_manifest:manifest,output_files_ref:{version:1,format:'json',sha256:hash(manifestBytes),bytes:manifestBytes.length}}
 const receipt={rows:{[name]:row},cleanup:{cleanup_complete:true,cleanup_validation:{[batch]:true},batches:{[batch]:close},custody:{[batch]:{sha256:journalHash}}}}
 const path=join(root,'results.json'),verdict=join(dir,'verdict.json'),outcomes:{case:string,result:string}[]=[]
 const invoke=()=>{json(path,receipt);return bindNativeReceipts(path,[verdict],[name])}
 assert.equal(invoke().control.synthetic,true);outcomes.push({case:'numeric-zero',result:'BINDER_ACCEPTED_SYNTHETIC_RECEIPT'})
 for(const [label,value] of [['string-zero','0'],['empty-array',[]],['array-zero',[0]],['null',null],['missing',undefined],['nonzero',1],['negative',-1],['boolean',false],['object',{}]] as const){
  if(value===undefined)delete row.placement.co_tenants;else row.placement.co_tenants=value
  assert.throws(invoke,/exclusive 16-CPU placement not observed/)
  outcomes.push({case:label,result:'REJECTED_AT_PLACEMENT_BOUNDARY'})
 }
 row.placement.co_tenants=0;assert.equal(invoke().control.synthetic,true)
 console.log(JSON.stringify({schema:'s51-native-binding-controls/v1',synthetic:true,nativeCustodyClaim:false,proofClaim:false,admissions:0,controls:outcomes.length,outcomes}))
}finally{rmSync(root,{recursive:true,force:true})}
