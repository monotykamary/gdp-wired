// Verify only a conditional structural bridge. Never infer target safety.
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {answers,gate} from '../../scripts/lean-gate/gate.ts'
const sha=(x:string|Buffer)=>createHash('sha256').update(x).digest('hex')
const read=(p:string)=>readFileSync(p,'utf8')
const model='3063304ae3bf8d7c7cc9870c838f7f5da7ab916a96d3729a7ca0b8db5f5b1d76'
const snapshot='2bef0af2d1fb819fa5f1f7ac67dc4cb27e6893e49775edf318a13be1f6f96ea5'
const required=['skt_target_identity','skt_source_view_nodes','skt_source_next_nodes','skt_source_maps_inv','skt_source_invariant','skt_q_eq','skt_view_eq','skt_maps_step','skt_step_eq','skt_admission','skt_init_state','skt_init_maps','skt_source_init','skt_source_reach','skt_source_public_law_conditional']
export function verifySktSource(directory:string){
 const source=JSON.parse(read(join(directory,'SOURCE-DATA.json')))
 if(source.protocol!=='sharded_kv'||source.brokenSource!==false||source.newProofSearches!==0||source.targetFamilyReplays!==0)throw Error('not unchanged sharded source')
 if(source.modelSHA256!==model||sha(readFileSync(join(directory,'SktSourceOriginal.ts')))!==model||source.leanSHA256!==sha(read(join(directory,'SktSourceDefs.lean')))||source.sourceSHA256!==sha(JSON.stringify({machine:source.machine,laws:source.laws})))throw Error('source data changed')
 if(source.sourceSHA256!=='cde3dda1297299928d310c5dd57ca96d97e3e90aa83489dfd42117f2241482e7'||source.leanSHA256!=='150babf4d07932842597d5d17783006cac52a8e7421f81cd88ad80e211e8b754')throw Error('not the pinned source AST')
 const basis=Array.from({length:44},(_,i)=>'unused$'+i)
 for(const [i,name] of [[0,'op'],[1,'n'],[2,'k'],[3,'v'],[4,'n2'],[5,'started'],[8,'key$2'],[9,'key$3'],[10,'key$4'],[11,'key$5'],[12,'key$6'],[31,'?unowned'],[32,'?allOwned'],[33,'?owns'],[34,'?starts'],[35,'?reshards'],[36,'?receives'],[37,'?puts'],[38,'w?unowned'],[39,'k$1'],[40,'k$2'],[41,'nodes'],[42,'keys'],[43,'values']] as [number,string][])basis[i]=name
 if(JSON.stringify(source.vars)!==JSON.stringify(basis)||JSON.stringify(source.maps)!==JSON.stringify(['Table','Owner','TransferMsg','Owned']))throw Error('source basis changed')
 const status=JSON.parse(read(join(directory,'SOURCE-STRUCTURAL-STATUS.json')))
 if(status.targetFamilyChecked!==false||status.sourceSafetyChecked!==false||status.newProofSearches!==0||status.targetFamilyReplays!==0||status.sourceSHA256!==source.sourceSHA256||status.targetSHA256!==snapshot)throw Error('wrong conditional-only status')
 const records=JSON.parse(read(join(directory,'LEAN-RECEIPTS.json'))) as {module:string,sourceSHA256:string,exitCode:number,reused?:boolean,oleanSHA256?:string}[]
 const modules:Record<string,unknown>={},found=new Set<string>(),files:Record<string,string>={}
 for(const r of records){
  if(!/^[A-Za-z][A-Za-z0-9]*$/.test(r.module)||r.exitCode!==0||modules[r.module])throw Error('invalid successful module receipt')
  const text=read(join(directory,r.module+'.lean')),olean=sha(readFileSync(join(directory,'rechecked',r.module+'.olean')))
  if(sha(text)!==r.sourceSHA256||r.oleanSHA256!==olean)throw Error('changed module '+r.module)
  let logSHA256:string|undefined
  if(r.module.startsWith('SktSource')){
   const log=read(join(directory,r.module+'.log')),errors=gate(log,[text],false)
   if(errors.length||/\.lean:\d+:\d+: error(?:\(|:)/.test(log))throw Error('module gate refused '+r.module)
   for(const a of answers(log))found.add(a.name)
   logSHA256=sha(log)
  }
  files[r.module+'.lean']=r.sourceSHA256
  modules[r.module]={sourceSHA256:r.sourceSHA256,oleanSHA256:olean,logSHA256,reused:!!r.reused}
 }
 for(const m of ['SktSourceDefs','SktSourceTarget','SktSourceInvariant','SktSourceBridge'])if(!modules[m])throw Error('missing module '+m)
 for(const n of required)if(!found.has(n))throw Error('missing required theorem '+n)
 if(files['Snapshot.lean']!==snapshot||files['Proofs.lean']!=='c09073712bcf85986273c9c8e037e1e8174597fcea285aa5c9c21315cff78baa'||files['ShardedSnapshotIdentity.lean']!=='5a98e4cd38fb0c97d86c683bea25e25671115066e9fa1408ba5192e500a17788')throw Error('wrong immutable target')
 return {schema:'bapa-skt-conditional-source/v1',status:'STRUCTURAL_BRIDGE_CHECKED',protocol:'sharded_kv',sourceReachIncluded:true,sourceSafetyChecked:false,targetSafetyRequired:true,targetFamilyChecked:false,allSizes:true,independentSizes:true,newProofSearches:0,targetFamilyReplays:0,sourceSHA256:source.sourceSHA256,modelSHA256:model,targetSHA256:snapshot,checkedTheorems:required,files,modules}
}
if(import.meta.main){
 const [directory,out]=process.argv.slice(2)
 if(!directory||!out)throw Error('usage: skt-source-verify.ts CHECKED_DIRECTORY NEW_RECEIPT')
 const result=verifySktSource(directory)
 writeFileSync(out,JSON.stringify(result,null,2)+'\n',{flag:'wx'});console.log(JSON.stringify(result))
}
