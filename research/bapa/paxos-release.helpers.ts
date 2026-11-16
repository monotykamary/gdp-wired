// Pure custody checks for the accepted Lean SOURCE capsule. No process execution.
import {lstatSync,readFileSync,readdirSync,realpathSync} from 'node:fs'
import {join,resolve,sep} from 'node:path'
import {assert,hash,hashFile,json,sameSet,verifyFiles} from './lift-regression.ts'
export {assert,hash,hashFile,json,sameSet,verifyFiles}
export const CAPSULE='research/bapa/paxos-accepted-capsule'
export const EVIDENCE='research/bapa/p2-paxos-accepted-results'
export const MANIFEST='b6fb06da57088b8c9c9a5434674b4a6d400b915ff654386070f803967b9e35de'
export const SOURCE_INPUTS:Record<string,string>={
 'research/protocols/ic3syn/p2-paxos-source-input.ts':'3063304ae3bf8d7c7cc9870c838f7f5da7ab916a96d3729a7ca0b8db5f5b1d76',
 'research/protocols/ic3syn/common.ts':'d84face9091688872b001f28d0ff31f1180590c57bf944efe6b32168651cd324'
}
export const REPRODUCED=['PaxosEprAtomicDefs.lean','source-machine.json','source-laws.json','basis.json','SOURCE-EMISSION.json']
export const TOOLCHAIN_IMPORTS=['Lean']
export const EMITTER='research/bapa/p2-paxos-atomic-export.ts'
export const CHECKED='b148b2a96fef429e50cc86e9c2e520e1f2b5b38ddf0f9a640655b8b7299fcba0'
export const MODE='hash-verified-retained-dependencies-fresh-literal-source-kernel' as const
export const PREFIX='Bapa.PaxosEprLiteral.'
export const FAMILY=PREFIX+'family_checked', SOURCE=PREFIX+'original_source_safety'
export const AXIOMS=['propext','Quot.sound']
export const SOURCE_AXIOMS=['propext','Classical.choice','Quot.sound']
export const FRESH=['PaxosEprLiteralFamily','PaxosEprLiteralGlobal','PaxosEprLiteralLinks',...Array.from({length:25},(_,i)=>'PaxosEprLiteralEntry'+i),'PaxosEprAccepted']
export const OWN=['paxos-release-replay.ts','paxos-release-audit.ts','paxos-release-replay.test.ts','paxos-release-replay.jobs.json','paxos-release.helpers.ts','paxos-release-base.helpers.json'].map(n=>'research/bapa/'+n).concat(EMITTER)
export type Checked={module:string;sha256:string;oleanSHA256:string;code:number;reused?:boolean;producer?:string}
export type Reused={module:string;sourceSha256:string;objectSha256:string;origin:'accepted-CHECKED'|'retained-core';dependencies:Record<string,string>;toolchainImports:string[]}
export type NativeCommand={label:string;argv:string[];cwd:string;environment:Record<string,string>;exitCode:number|null;signal:string|null;stdout:string;stderr:string;stdoutSha256:string;stderrSha256:string}
export type PaxosReplayReceipt={schema:'paxos-release-replay/v1';id:'paxos_epr';status:'SOURCE_CHECKED'|'FAILED';mode:typeof MODE;format:'Lean-source';nativeCliAcceptance:false;cleanSourceBuild:false;noSearch:true;claimedSnapshot:string;implementationFiles:Record<string,string>;implementationSha256:string;runnerFiles:Record<string,string>;runnerSha256:string;capsuleManifestSha256:string;sourceFiles:Record<string,string>;sourcePortSha256:string;checkedSha256:string;familyTheorem:typeof FAMILY;sourceTheorem:typeof SOURCE;entries:number[];obligations:{law:number;step:boolean}[];axioms:Record<string,string[]>;reused:Reused[];fresh:{module:string;sourceSha256:string;objectSha256:string}[];commands:NativeCommand[];originalExports:Record<string,unknown>;sourceInputFiles:Record<string,string>;sourceReproductionFiles:Record<string,string>;reachableModules:string[];toolchainModules:Record<string,string>;lean?:{path:string;sha256:string;version:string};reason?:string}
export function runnerFiles(root:string){return Object.fromEntries(OWN.map(p=>[p,hashFile(join(root,p))]))}
export function regular(directory:string,name:string){
 const base=realpathSync(directory),p=resolve(directory,name)
 assert(p.startsWith(resolve(directory)+sep),'unsafe file '+name)
 const st=lstatSync(p);assert(st.isFile()&&!st.isSymbolicLink()&&realpathSync(p).startsWith(base+sep),'non-regular file '+name)
 return p
}
export function checkedFile(directory:string,name:string,digest:string){const p=regular(directory,name);assert(hashFile(p)===digest,'file changed: '+name);return p}
export function capsuleFiles(directory:string,root=process.cwd()):Record<string,string>{
 checkedFile(directory,'SHA256SUMS',MANIFEST)
 const files:Record<string,string>={},external:string[]=[]
 const lines=readFileSync(join(directory,'SHA256SUMS'),'utf8').trimEnd().split('\n')
 assert(lines.length===145,'incomplete capsule manifest')
 for(const line of lines){
  const ext=/^([a-f0-9]{64})  (\.\.\/\.\.\/protocols\/ic3syn\/(p2-paxos-source-input|common)\.ts)$/.exec(line)
  if(ext){
   const path='research/protocols/ic3syn/'+ext[3]+'.ts'
   assert(SOURCE_INPUTS[path]===ext[1],'external source pin differs')
   checkedFile(root,path,ext[1]!);external.push(path);continue
  }
  const m=/^([a-f0-9]{64})  ([A-Za-z0-9_.-]+)$/.exec(line);assert(m,'bad capsule manifest line')
  assert(!Object.hasOwn(files,m[2]!),'duplicate source');files[m[2]!]=m[1]!
 }
 sameSet(external,Object.keys(SOURCE_INPUTS),'explicit source port paths')
 assert(Object.keys(files).length===143,'incomplete source corpus');verifyFiles(directory,files)
 const e=json<{sourcePortSha256:string;newProofSearches:number;files:Record<string,string>}>(join(directory,'SOURCE-EMISSION.json'))
 assert(e.sourcePortSha256==='3063304ae3bf8d7c7cc9870c838f7f5da7ab916a96d3729a7ca0b8db5f5b1d76'&&e.newProofSearches===0,'source port binding')
 for(const [n,h] of Object.entries(e.files))assert(files[n]===h,'source emission binding '+n)
 return files
}
export function acceptedRows(root:string,files:Record<string,string>):Checked[]{
 const path=checkedFile(join(root,EVIDENCE),'CHECKED.json',CHECKED),rows=json<Checked[]>(path)
 assert(rows.length===114,'incomplete accepted CHECKED');sameSet(rows.map(r=>r.module),[...new Set(rows.map(r=>r.module))],'duplicate CHECKED')
 for(const r of rows){assert(r.code===0&&files[r.module+'.lean']===r.sha256&&/^[a-f0-9]{64}$/.test(r.oleanSHA256),'accepted source/object binding '+r.module)}
 return rows
}
export function imports(directory:string,module:string){
 return [...readFileSync(join(directory,module+'.lean'),'utf8').matchAll(/^import ([A-Za-z0-9_ ]+)$/gm)].flatMap(m=>m[1]!.trim().split(/\s+/))
}
export function reachableModules(directory:string,files:Record<string,string>,rootModule='PaxosEprAccepted'){
 const modules=new Set<string>(),external=new Set<string>()
 function visit(module:string){
  if(TOOLCHAIN_IMPORTS.includes(module)){external.add(module);return}
  assert(files[module+'.lean'],'missing reachable import '+module)
  if(modules.has(module))return
  modules.add(module)
  for(const dependency of imports(directory,module))visit(dependency)
 }
 visit(rootModule)
 return {modules:[...modules].sort(),external:[...external].sort()}
}
export function dependencyMap(directory:string,module:string,objects:Record<string,string>,external:string[]=[]){
 return Object.fromEntries(imports(directory,module).filter(n=>!external.includes(n)).map(n=>{assert(objects[n],'unbound imported object '+module+' -> '+n);return [n,objects[n]!] }))
}
export function checkAxioms(log:string,expected:Record<string,string[]>){
 assert(!/\bsorry\b|\bunsound\b|\berror:|declaration uses 'sorry'/i.test(log),'Lean diagnostic refused')
 const got:Record<string,string[]>={}
 for(const m of log.matchAll(/'([^']+)' depends on axioms: \[([^\]]*)\]/g)){
  assert(!Object.hasOwn(got,m[1]!),'duplicate axiom output');got[m[1]!]=m[2]!.split(',').map(s=>s.trim()).filter(Boolean)
 }
 sameSet(Object.keys(got),Object.keys(expected),'axiom theorem names')
 for(const [n,a] of Object.entries(expected))assert(JSON.stringify(got[n])===JSON.stringify(a),'exact axiom mismatch '+n)
 return got
}
export function expectedAxioms(module:string):Record<string,string[]>{
 assert(FRESH.includes(module),'unexpected fresh module '+module)
 let names:string[]=[],axioms=AXIOMS
 if(module==='PaxosEprLiteralFamily')names=['entries_exact']
 else if(module==='PaxosEprLiteralGlobal'){names=['global_checked'];axioms=['propext']}
 else if(module==='PaxosEprLiteralLinks')names=['link7','link10','link20','step7_checked','step10_checked','step20_checked']
 else if(/^PaxosEprLiteralEntry\d+$/.test(module)){
  const index=Number(module.replace('PaxosEprLiteralEntry',''))
  names=['entry'+index+'_checked']
  // Retained logs: direct kernel-decision entries need only propext;
  // the three transported quotient-tree entries also need Quot.sound.
  if(![7,10,20].includes(index))axioms=['propext']
 }else if(module==='PaxosEprAccepted')return {[FAMILY]:AXIOMS,[SOURCE]:SOURCE_AXIOMS}
 else throw Error('unexpected fresh module '+module)
 return Object.fromEntries(names.map(n=>[PREFIX+n,axioms]))
}
export function validateCoverage(entries:number[],obligations:{law:number;step:boolean}[]){
 assert(Array.isArray(entries)&&JSON.stringify(entries)===JSON.stringify(Array.from({length:25},(_,i)=>i)),'incomplete entries')
 assert(Array.isArray(obligations)&&obligations.length===50,'incomplete obligations')
 sameSet(obligations.map(r=>{assert(typeof r.step==='boolean'&&Number.isInteger(r.law),'malformed obligation');return r.law+':'+r.step}),Array.from({length:25},(_,i)=>[i+':false',i+':true']).flat(),'obligations')
}
export function exactObject(actual:unknown,expected:unknown,label:string){assert(JSON.stringify(actual)===JSON.stringify(expected),label+' differs')}
export function noExtraObjects(directory:string,expected:string[]){sameSet(readdirSync(directory).filter(n=>n.endsWith('.olean')),expected.map(n=>n+'.olean'),'object closure')}
