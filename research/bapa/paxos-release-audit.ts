// Import-safe, filesystem-only audit. Never starts Lean, a shell, search, or an agent.
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {implementationFiles} from './lift-regression.ts'
import {AXIOMS,CAPSULE,CHECKED,EMITTER,FAMILY,FRESH,MANIFEST,MODE,REPRODUCED,SOURCE,SOURCE_AXIOMS,SOURCE_INPUTS,TOOLCHAIN_IMPORTS,imports,reachableModules,acceptedRows,assert,capsuleFiles,checkAxioms,checkedFile,dependencyMap,exactObject,expectedAxioms,hash,json,noExtraObjects,runnerFiles,sameSet,validateCoverage,verifyFiles,type PaxosReplayReceipt,type Reused} from './paxos-release.helpers.ts'
export type {PaxosReplayReceipt} from './paxos-release.helpers.ts'
export type BasePins={origin:string;files:Record<string,string>;objects:Record<string,string>;exports:Record<string,{manifestSha256:string;resultsSha256:string;job:string;batch:string}>}
export function expectedReuse(root:string,files:Record<string,string>){
 const rows=acceptedRows(root,files),base=json<BasePins>(join(root,'research/bapa/paxos-release-base.helpers.json'))
 assert(Object.keys(base.objects).length===22,'incomplete retained core pins')
 const objects:Record<string,string>={...base.objects}
 for(const r of rows){if(objects[r.module])assert(objects[r.module]===r.oleanSHA256,'overlapping dependency mismatch '+r.module);objects[r.module]=r.oleanSHA256}
 const modules=Object.keys(files).filter(n=>n.endsWith('.lean')&&n!=='lakefile.lean').map(n=>n.slice(0,-5))
 sameSet(Object.keys(objects),modules,'source/object coverage')
 const reachable=reachableModules(join(root,CAPSULE),files)
 const reused:Reused[]=reachable.modules.filter(n=>!FRESH.includes(n)).map((module):Reused=>{
  const dependencies=dependencyMap(join(root,CAPSULE),module,objects,TOOLCHAIN_IMPORTS)
  for(const n of Object.keys(dependencies))assert(!FRESH.includes(n),'retained module depends on replaced fresh object '+module)
  return {module,sourceSha256:files[module+'.lean']!,objectSha256:objects[module]!,origin:base.objects[module]?'retained-core':'accepted-CHECKED',dependencies,toolchainImports:imports(join(root,CAPSULE),module).filter(n=>TOOLCHAIN_IMPORTS.includes(n))}
 })
 return {rows,base,objects,reused,reachable}
}
// These manifests were the native export receipts, not hashes invented by this runner.
export function verifyOriginalExports(directory:string,root:string,files:Record<string,string>){
 const {base,rows}=expectedReuse(root,files)
 for(const [kind,pin]of Object.entries(base.exports)){
  const manifest=checkedFile(directory,kind+'-export.json',pin.manifestSha256)
  const results=json<any>(checkedFile(directory,kind+'-results.json',pin.resultsSha256))
  const row=results.rows?.[pin.job]
  assert(row?.code===0&&row.status==='SUCCEEDED'&&row.batch===pin.batch&&row.strict_once===true&&row.attempts===1&&row.max_attempts===1&&results.cleanup?.cleanup_complete===true,'original native result not accepted')
  assert(row.output_files_ref?.sha256===pin.manifestSha256&&row.output_files_ref.bytes===readFileSync(manifest).length,'native export reference mismatch')
  const entries=json<{path:string;sha256:string;bytes:number;format:string}[]>(manifest)
  sameSet(entries.map(e=>e.path),[...new Set(entries.map(e=>e.path))],'duplicate export path')
  const expected:Record<string,string>={}
  if(kind==='base'){
   for(const [module,digest]of Object.entries(base.objects)){
    expected['project/'+module+'.lean']=files[module+'.lean']!
    expected['project/.lake/build/lib/lean/'+module+'.olean']=digest
   }
   for(const [name,digest]of Object.entries(base.files))expected[name]=digest
  }else{
   expected['CHECKED.json']=CHECKED
   for(const r of rows){expected[r.module+'.lean']=r.sha256;expected['checked/'+r.module+'.olean']=r.oleanSHA256}
  }
  for(const [path,digest]of Object.entries(expected)){
   const e=entries.find(e=>e.path===path);assert(e?.sha256===digest&&e.format==='file'&&Number.isSafeInteger(e.bytes),'original export does not bind '+kind+':'+path)
  }
 }
 return base.exports
}
export function auditPaxosReplay(directory:string,root=process.cwd()):PaxosReplayReceipt{
 const r=json<PaxosReplayReceipt>(join(directory,'PAXOS-REPLAY.json'))
 assert(r.schema==='paxos-release-replay/v1'&&r.status==='SOURCE_CHECKED'&&r.id==='paxos_epr','Paxos replay did not accept')
 assert(r.mode===MODE&&r.format==='Lean-source'&&r.noSearch===true&&r.nativeCliAcceptance===false&&r.cleanSourceBuild===false,'Paxos replay qualification changed')
 assert(typeof r.claimedSnapshot==='string'&&r.claimedSnapshot.length>0,'missing claimedSnapshot')
 const implementation=implementationFiles(root),own=runnerFiles(root)
 exactObject(r.implementationFiles,implementation,'implementation files');assert(r.implementationSha256===hash(JSON.stringify(implementation)),'implementation hash mismatch')
 exactObject(r.runnerFiles,own,'runner files');assert(r.runnerSha256===hash(JSON.stringify(own)),'runner hash mismatch')
 assert(r.capsuleManifestSha256===MANIFEST&&r.checkedSha256===CHECKED,'manifest binding mismatch')
 assert(r.sourcePortSha256==='3063304ae3bf8d7c7cc9870c838f7f5da7ab916a96d3729a7ca0b8db5f5b1d76','source port hash mismatch')
 assert(r.familyTheorem===FAMILY&&r.sourceTheorem===SOURCE,'required theorem names changed')
 validateCoverage(r.entries,r.obligations)
 const files=capsuleFiles(join(root,CAPSULE),root);exactObject(r.sourceFiles,files,'capsule source inventory')
 const project=join(directory,'project');verifyFiles(project,files);checkedFile(project,'SHA256SUMS',MANIFEST)
 exactObject(r.sourceInputFiles,SOURCE_INPUTS,'source input inventory');verifyFiles(join(directory,'source-inputs'),SOURCE_INPUTS)
 const reproduction=Object.fromEntries(REPRODUCED.map(n=>[n,files[n]!]))
 exactObject(r.sourceReproductionFiles,reproduction,'source reproduction inventory');verifyFiles(join(directory,'source-reproduction'),reproduction)
 for(const name of REPRODUCED)assert(readFileSync(join(directory,'source-reproduction',name)).equals(readFileSync(join(project,name))),'source reproduction bytes changed '+name)
 const {base,objects,reused,reachable}=expectedReuse(root,files)
 exactObject(r.reused,reused,'reused source-object provenance')
 exactObject(r.originalExports,verifyOriginalExports(join(directory,'provenance'),root,files),'original export provenance')
 checkedFile(directory,'provenance/CHECKED.json',CHECKED)
 for(const [name,digest]of Object.entries(base.files))checkedFile(directory,'provenance/base/'+name,digest)
 assert(r.fresh.length===FRESH.length,'incomplete fresh checks');exactObject(r.fresh.map(x=>x.module),FRESH,'fresh check order')
 for(const row of r.reused)checkedFile(project,'checked/'+row.module+'.olean',row.objectSha256)
 for(const row of r.fresh){assert(row.sourceSha256===files[row.module+'.lean'],'fresh source binding mismatch');checkedFile(project,'checked/'+row.module+'.olean',row.objectSha256)}
 exactObject(r.reachableModules,reachable.modules,'reachable module closure')
 noExtraObjects(join(project,'checked'),reachable.modules)
 sameSet(Object.keys(r.toolchainModules),reachable.external,'toolchain imports')
 for(const [module,digest]of Object.entries(r.toolchainModules))checkedFile(directory,'runtime/'+module+'.olean',digest)
 assert(r.lean&&r.lean.path.startsWith('/')&&/^[a-f0-9]{64}$/.test(r.lean.sha256),'Lean executable binding missing')
 assert(r.commands.length===FRESH.length+3,'incomplete native commands')
 exactObject(r.commands.map(c=>c.label),['source-emission','lean-path','lean-version',...FRESH],'native command order')
 const axioms:Record<string,string[]>={}
 for(const c of r.commands){
  assert(c.exitCode===0&&c.signal===null&&c.cwd===(c.label==='source-emission'?'root':'project'),'native command failed '+c.label)
  exactObject(c.environment,{LEAN_PATH:'project/checked',LEAN_NUM_THREADS:'1',GDP_LEAN_NATIVE:'0',...(c.label==='source-emission'?{SUPERCOMPUTER_OUTPUT_DIR:'source-reproduction'}:{})},'native environment')
  assert(c.stdout==='logs/'+c.label+'.stdout.log'&&c.stderr==='logs/'+c.label+'.stderr.log','unsafe log path')
  const out=readFileSync(checkedFile(directory,c.stdout,c.stdoutSha256),'utf8'),err=readFileSync(checkedFile(directory,c.stderr,c.stderrSha256),'utf8')
  if(c.label==='source-emission'){
   exactObject(c.argv,['timeout','--kill-after=10s','120s','bun',EMITTER],'source emission command')
  }else if(c.label==='lean-path'){
   exactObject(c.argv,['elan','which','lean'],'Lean path command');assert(out.trim()===r.lean.path&&err.trim()==='','Lean path result')
  }else if(c.label==='lean-version'){
   exactObject(c.argv,[r.lean.path,'--version'],'Lean version command')
   assert(out===r.lean.version&&/^Lean \(version 4\.34\.0(?:,|\))/.test(out),'wrong Lean version')
  }else{
   exactObject(c.argv,['timeout','--kill-after=10s','300s',r.lean.path,'-o','checked/'+c.label+'.olean',c.label+'.lean'],'native Lean command')
   Object.assign(axioms,checkAxioms(out+'\n'+err,expectedAxioms(c.label)))
  }
 }
 exactObject(r.axioms,axioms,'recorded axioms')
 exactObject(r.axioms[FAMILY],AXIOMS,'family axioms');exactObject(r.axioms[SOURCE],SOURCE_AXIOMS,'source axioms')
 // The claim is a fresh final source/kernel check over verified retained imports,
 // not a clean source rebuild or native data-only CLI lift.
 return r
}
