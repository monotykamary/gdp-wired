// No search: hash-bound old proof, current source definitions, and Lean inclusion.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {readCertificateGraph} from './proof-codec.ts'
import {restoreTermPrelude} from './proof-prelude.ts'
import {leanProject,retainedCMachineToLean} from '../../lean-kernel/emit.ts'
import {boundOf,witnessesOf,postName} from '../../kernel/kernel.ts'
import {alphaProposals} from './source-projection.ts'
import type {Machine} from '../../core/machine.ts'
const hash=(x:string|Uint8Array)=>createHash('sha256').update(x).digest('hex')
const [capture,proofPath,out]=process.argv.slice(2)
if(!capture||!proofPath||!out)throw Error('usage: p2-toy-inclusion.ts CAPTURE PROOFS NEW_PROJECT')
const capRaw=readFileSync(join(capture,'CAPTURE.json')),inputSha256=hash(capRaw)
if(inputSha256!=='33f1a9949fb71fec0b5c1017c0607b25517a4222de10f0634bddc9bd4d8ae84b')throw Error('wrong capsule')
const raw=readFileSync(proofPath,'utf8')
if(hash(raw)!=='27b6b6c2295c7e444999c16e84abd7e56e871f2d4100b39980af416a5cd7b1bf')throw Error('wrong retained Lean source')
const cap=JSON.parse(capRaw.toString()),meta:[object,unknown][]=[]
const data=readCertificateGraph(join(capture,'graph'),cap.graphManifestSha256,{maxBytes:536870912,maxNodes:4000000,maxStrings:200000,maxArrayLength:2000000,maxShards:2048},(o,m)=>meta.push([o,m])) as any
restoreTermPrelude(data.terms,meta)
const {protocols}=await import('../protocols/ic3syn/models.ts')
const p=protocols.find(p=>p.id==='toy_consensus_forall')!,r=p.make(),laws=p.laws(r),source:Machine=r.machine,producer:Machine=data.final.machine
const vars=new Set<string>([...source.params,...source.inputs,...Object.keys(source.state)]),maps=new Set<string>([...Object.keys(source.maps??{}),...(source.inputMaps??[])])
function visit(x:any):void{if(!x||typeof x!=='object')return;if(Array.isArray(x)){x.forEach(visit);return}if(x.op==='var')vars.add(x.name);if(x.op==='get')maps.add(x.map);Object.values(x).forEach(visit)}
visit(source);visit(laws)
for(const [name,q]of Object.entries(source.step.flags??{})){vars.add('?'+name);if(q.op==='all'){boundOf(q).forEach(x=>vars.add(x));witnessesOf(name,q).forEach(x=>vars.add(x))}}
for(const l of laws){if(l.forall)vars.add(l.forall);l.keys?.forEach(x=>vars.add(x))}
for(const [name,d]of Object.entries(source.counts??{})){maps.add(name);maps.add(postName(name));vars.add(d.j);vars.add(d.key);vars.add(d.lo??d.j)}
const renames=alphaProposals(source,producer)
for(const r of renames){vars.add('?'+r.flag);vars.add(r.old);vars.add(r.fresh)}
const erase=(x:any):any=>{if(!x||typeof x!=='object')return x;if(Array.isArray(x))return x.map(erase);if(['<','<='].includes(x.op)&&x.b?.op==='const'&&x.b.value===64)return {op:'<=',a:{op:'const',value:0},b:{op:'const',value:0}};return Object.fromEntries(Object.entries(x).map(([k,v])=>[k,erase(v)]))}
let defs='',basisInfo:unknown
const normalize=(m:any)=>({...m,counts:undefined,inputMaps:[...(m.inputMaps??[]),...Object.keys(m.counts??{})]})
retainedCMachineToLean('p2_unused',producer,data.final.laws,data.final.proof,{extraVars:[...vars],extraMaps:[...maps],after:b=>{
 const law=laws[0]!,strong=erase(data.final.laws[2]);basisInfo={vars:b.vars,maps:b.maps}
 defs=`import ToyConsensusForallTransport\nimport QAlpha\nopen Kern\ndef p2_basis_machine : SMachine := ${b.machine(normalize(producer))}\ndef p2_source : SMachine := ${b.machine(normalize(source))}\ndef p2_source_decls : List CDecl := ${b.decls(source.counts)}\ndef p2_source_renames : List QAlpha.Rename := [${renames.map(r=>`⟨${b.ix('?'+r.flag)}, ${b.ix(r.old)}, ${b.ix(r.fresh)}⟩`).join(', ')}]\ndef p2_fresh : List Nat := [${Object.keys(producer.counts??{}).filter(k=>!Object.hasOwn(source.counts??{},k)).map(b.mx).join(', ')}]\ndef p2_source_law : MLaw := ⟨${b.condition(law.holds)}, some ${b.ix(law.forall!)}⟩\ndef p2_unbounded_law : MLaw := ⟨${b.condition(strong.holds)}, some ${b.ix(strong.forall)}⟩\ndef p2_source_keys : List Nat := [${law.keys!.map(b.ix).join(', ')}]\ndef p2_source_assume : C := ${b.condition(source.assume!)}\ndef p2_target_assume : C := ${b.condition(erase(producer.assume))}\n`
 return ''
}})
const project=leanProject(raw,{name:'Proofs'})
project['Proofs.lean']=raw
for(const name of ['CertificateBoundErasure','ToyConsensusForallTransport','CountedSourceProjection','CountedNoninterference','CountedSourceBridge','SourceInclusion','SourceInclusionControls'])project[name+'.lean']=readFileSync(new URL('./'+name+'.lean',import.meta.url),'utf8')
project['P2SourceDefs.lean']=defs
project['BapaProof.lean']=readFileSync(new URL('./P2ToySource.lean',import.meta.url),'utf8')
project['source-machine.json']=JSON.stringify(source,null,2)+'\n';project['source-laws.json']=JSON.stringify(laws,null,2)+'\n';project['basis.json']=JSON.stringify(basisInfo,null,2)+'\n'
const modules=Object.keys(project).filter(n=>n.endsWith('.lean')&&n!=='lakefile.lean').map(n=>n.slice(0,-5))
project['lakefile.lean']='import Lake\nopen Lake DSL\npackage p2source\n@[default_target]\nlean_lib BapaSource where\n  roots := #['+modules.map(n=>'`'+n).join(', ')+']\n'
mkdirSync(out)
for(const [name,text]of Object.entries(project))writeFileSync(join(out,name),text,{flag:'wx'})
const receipt={schema:'bapa-emission/v1',status:'EMITTED_NOT_CHECKED',inputSha256,identity:{...cap.identity,sourcePortSha256:hash(readFileSync(new URL('../protocols/ic3syn/models.ts',import.meta.url))),retainedLeanSha256:hash(raw),transportModuleSha256:hash(project['ToyConsensusForallTransport.lean']!)},files:Object.fromEntries(Object.entries(project).map(([n,t])=>[n,hash(t)])),familyTheorem:'bapa_toy_consensus_forall_transported_laws',leanVersion:'4.34.0',leanExecuted:false,allSizesProven:false,sourceProjection:{kind:'counted',method:'alpha-counted-inclusion-law-implication',sourceTheorems:['bapa_toy_consensus_forall_source_law0_holds'],sourceLawNames:laws.map(l=>l.name)}}
writeFileSync(join(out,'EMITTED.json'),JSON.stringify(receipt,null,2)+'\n',{flag:'wx'})
console.log(JSON.stringify({status:receipt.status,inputSha256,sourcePortSha256:receipt.identity.sourcePortSha256}))
