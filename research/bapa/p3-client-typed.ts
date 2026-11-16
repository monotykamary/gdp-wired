// No search: exact retained family, current source, and explicit bridge checks.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {readCertificateGraph} from './proof-codec.ts'
import {restoreTermPrelude} from './proof-prelude.ts'
import {leanProject,retainedSMachineToLean} from '../../lean-kernel/emit.ts'
import {boundOf,witnessesOf,substC} from '../../kernel/kernel.ts'
import type {Machine} from '../../core/machine.ts'
const sha=(x:string|Uint8Array)=>createHash('sha256').update(x).digest('hex')
const [capture,proofPath,out]=process.argv.slice(2)
if(!capture||!proofPath||!out)throw Error('usage: p3-client-inclusion.ts CAPTURE PROOFS OUT')
const capBytes=readFileSync(join(capture,'CAPTURE.json')),cap=JSON.parse(capBytes.toString())
if(sha(capBytes)!=='e76ed2d24da036b98a98ea1edf509abe741499a2647c88f647c4d4f235cc87f0')throw Error('wrong capsule')
const raw=readFileSync(proofPath,'utf8')
if(sha(raw)!=='8d629dfe6d70661809e378ab21ec738a5173613cf1796473f3032942b1f7dbce')throw Error('wrong retained Lean')
const meta:[object,unknown][]=[]
const data=readCertificateGraph(join(capture,'graph'),cap.graphManifestSha256,{maxBytes:536870912,maxNodes:4000000,maxStrings:200000,maxArrayLength:2000000,maxShards:2048},(o,m)=>meta.push([o,m])) as any
restoreTermPrelude(data.terms,meta)
let leaf=data.proof
while(leaf.kind==='derived'){if(leaf.parents.length!==1)throw Error('ambiguous producer');leaf=leaf.parents[0]}
if(leaf.kind!=='usual')throw Error('expected usual leaf')
const {protocols}=await import('../protocols/ic3syn/models.ts')
const p=protocols.find(p=>p.id==='client_server_db_ae')!,r=p.make(),laws=p.laws(r),source:Machine=r.machine
const names=new Set<string>([...source.params,...source.inputs,...Object.keys(source.state)])
function visit(x:any):void{if(!x||typeof x!=='object')return;if(Array.isArray(x)){x.forEach(visit);return}if(x.op==='var')names.add(x.name);Object.values(x).forEach(visit)}
visit(source);visit(laws)
for(const [f,q]of Object.entries(source.step.flags??{})){names.add('?'+f);if(q.op==='all'){boundOf(q).forEach(x=>names.add(x));witnessesOf(f,q).forEach(x=>names.add(x))}}
for(const l of laws){if(l.forall)names.add(l.forall);l.keys?.forEach(x=>names.add(x));l.some?.forEach(x=>names.add(x))}
let defs='',transport='',basis:any
retainedSMachineToLean('p3_basis_check',leaf.machine,leaf.laws,leaf.proof,{free:[...names],after:(ix,mx,lit,c)=>{
 const sizeNames=['nodes','requestSize','responses','ids'],sizes=sizeNames.map(ix)
 const signature:Record<string,number[]>={Match:[1,2],RequestSent:[0,1],ResponseSent:[0,2],ResponseReceived:[0,2],DbRequestSent:[3,1],DbResponseSent:[3,2],T:[3,0],'DbResponseSent$g':[3,2],'ResponseSent$w':[0,2],'DbRequestSent$g':[3,1]}
 const values:Record<string,number>={'DbResponseSent$g':1,'ResponseSent$w':1,'DbRequestSent$g':0}
 const q=Object.values(source.step.flags??{}).find(q=>q.op==='all')!
 if(q.op!=='all')throw Error('missing source quantified flag')
 const oldq=Object.values(leaf.machine.step.flags).find((q:any)=>q.op==='all') as any
 const sourceKey=boundOf(q)[0]!,targetKey=boundOf(oldq)[0]!
 const fixed:Record<string,number>={n:0,r:1,p:2,i:3,[targetKey]:0,'w?noneWithId':0}
 const scope=(law?:any)=>{
   const roles={...fixed}
   const put=(name:string,sort:number)=>{if(roles[name]!==undefined&&roles[name]!==sort)throw Error(`mixed sort ${law?.name??'machine'}: ${name}`);roles[name]=sort}
   const tuple=(e:any):any[]=>e.op==='tup'?[e.a,...tuple(e.b)]:[e]
   const assign=(e:any,sort:number):void=>{
     if(e.op==='var')put(e.name,sort)
     else if(e.op==='get'){if(values[e.map]!==sort)throw Error('unclassified coordinate '+e.map)}
     else if(e.op==='const')return
     else if(e.op==='if'){assign(e.yes??e.a,sort);assign(e.no??e.b,sort)}
     else throw Error('unclassified coordinate '+e.op)
   }
   const walk=(x:any):void=>{if(!x||typeof x!=='object')return;if(Array.isArray(x)){x.forEach(walk);return}
     if(x.op==='get'){const ss=signature[x.map];if(!ss)throw Error('unknown map '+x.map);const ks=tuple(x.key);if(ks.length!==ss.length)throw Error('wrong tuple '+x.map);ks.forEach((k,i)=>assign(k,ss[i]!))}
     Object.values(x).forEach(walk)
   }
   if(law){walk(law.holds);for(const k of [law.forall,...(law.keys??[])].filter(Boolean)){if(roles[k]===undefined)throw Error('unclassified binder '+k);put(k+'#',roles[k]!)}}
   return roles
 }
 const scopes=leaf.laws.map((l:any)=>scope(l)),base=scope()
 const typing=(roles:Record<string,number>)=>`⟨[${sizes.join(',')}], [${Object.entries(roles).map(([v,s])=>`(${ix(v)},${sizes[s]})`).join(',')}], [${Object.entries(values).map(([m,s])=>`(${mx(m)},${sizes[s]})`).join(',')}]⟩`
 basis={vars:Object.fromEntries([...names].map(n=>[n,ix(n)])),maps:Object.fromEntries(Object.keys(signature).map(n=>[n,mx(n)])),sizes,base,scopes,sourceBinder:ix(sourceKey),targetBinder:ix(targetKey)}
 transport=`import Proofs\nimport CertificateBoundSubstitution\nimport BoundErasureReplay\nopen Kern\nnamespace P3Typed\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nopen Bapa.CertificateBoundSubstitution\ndef baseTyping : Typed.Typing := ${typing(base)}\ndef typings : List Typed.Typing := [${scopes.map(typing).join(',\n')}]\ndef machineOption := Typed.machine 64 baseTyping captured_client_server_db_ae_0_machine\ndef machine : SMachine := machineOption.getD captured_client_server_db_ae_0_machine\ndef entryAt (i : Nat) (p : Typed.Typing) (original : SEntry) : Option SEntry := let e := Typed.withoutStepCache original; if [0,1,2,26].contains i then Typed.entryWithoutInitialCache 64 p e else Typed.entry 64 p e\ndef entryOptions : List (Option SEntry) := (typings.zip captured_client_server_db_ae_0_proof).zipIdx.map fun ((p,e),i) => entryAt i p e\ndef proof : List SEntry := (entryOptions.zip captured_client_server_db_ae_0_proof).map fun (x,e) => x.getD e\n#eval (show IO Unit from do\n  let out ← IO.getEnv \"SUPERCOMPUTER_OUTPUT_DIR\"\n  let directory := out.getD \".\"\n  let mut rows := [\"law\\tlaw_ok\\tstart_ok\\tstep_ok\\tentry_ok\"]\n  for ((p,e),i) in (typings.zip captured_client_server_db_ae_0_proof).zipIdx do\n    rows := rows ++ [s!\"{i}\\t{(Typed.law 64 p e.law).isSome}\\t{(Typed.certificate 64 p (if [0,1,2,26].contains i then (e.start.1,[],e.start.2.2) else e.start)).isSome}\\t{(Typed.certificate 64 p (Typed.withoutStepCache e).step).isSome}\\t{(entryAt i p e).isSome}\"]\n  IO.FS.writeFile (directory ++ \"/typed-options.tsv\") (String.intercalate \"\\n\" rows ++ \"\\n\")\n  if !machineOption.isSome || !entryOptions.all Option.isSome then\n    throw (IO.userError \"typed annotation gap: see typed-options.tsv\")\n  Bapa.BoundErasureReplay.emitPlain directory \"P3TypedClient\" \"P3Typed\" machine proof 6)\nend P3Typed\n`
 const lift=(x:any,roles:Record<string,number>):any=>{
   if(!x||typeof x!=='object')return x
   if(Array.isArray(x))return x.map(v=>lift(v,roles))
   if((x.op==='<'||x.op==='<=')&&x.b.op==='const'&&x.b.value===64){
     const s=x.a.op==='var'?roles[x.a.name]:x.a.op==='get'?values[x.a.map]:undefined
     if(s===undefined)throw Error('untyped expression bound')
     return {...x,a:lift(x.a,roles),b:{op:'var',name:sizeNames[s]}}
   }
   return Object.fromEntries(Object.entries(x).map(([k,v])=>[k,lift(v,roles)]))
 }
 const witness={op:'get' as const,map:'ResponseSent$w',key:{op:'tup' as const,a:{op:'var' as const,name:laws[0]!.forall!},b:{op:'var' as const,name:laws[0]!.keys![0]!}}}
 const weak=substC(laws[0]!.holds,{vars:{[laws[0]!.some![0]!]:witness},maps:{},flags:{}})
 const sigma=`[(${ix(laws[0]!.some![0]!)}, .get ${mx('ResponseSent$w')} (.tup (.var ${ix(laws[0]!.forall!)}) (.var ${ix(laws[0]!.keys![0]!)})))]`
 defs=`import P3TypedClient\nimport SourceInclusion\nimport BoundGhost\nimport QAlpha\nopen Kern\ndef p3_basis : SMachine := ${lit(leaf.machine)}\ndef p3_source : SMachine := ${lit(source)}\ndef p3_renames : List QAlpha.Rename := [⟨${ix('?noneWithId')},${ix(sourceKey)},${ix(targetKey)}⟩]\ndef p3_source_alpha := QAlpha.renameAll p3_source p3_renames\nabbrev p3_target := P3Typed.machine\ndef p3_ghosts : SGhostedM := ⟨p3_source_alpha, [], p3_target.f.m.maps0.drop 7, p3_target.f.m.writes.drop 7, []⟩\ndef p3_source_body : C := ${c(laws[0]!.holds)}\ndef p3_sigma : List (Nat × E) := ${sigma}\ndef p3_source_assume : C := ${c(source.assume!)}\ndef p3_typed_assume : C := ${c(lift(leaf.machine.assume,base))}\ndef p3_strong_literal : C := ${c(lift(leaf.laws[0].holds,scopes[0]))}\ndef p3_weak_literal : C := ${c(weak)}\ndef p3_strong_body : C := (P3Typed.proof[0]'(by decide +kernel)).law.holds\ndef p3_weak_body : C := substC p3_sigma p3_source_body\ndef p3_source_keys : List Nat := [${laws[0]!.keys!.map(ix).join(',')}]\ndef p3_source_key : Option Nat := some ${ix(laws[0]!.forall!)}\ndef p3_source_exists : List Nat := [${laws[0]!.some!.map(ix).join(',')}]\n`
 return ''
}})
const project=leanProject(raw,{name:'Proofs'})
project['Proofs.lean']=raw
for(const name of ['CertificateBoundErasure','CertificateBoundSubstitution','TypedBoundControls','BoundErasureReplay','CountedSourceProjection','CountedNoninterference','CountedSourceBridge','SourceInclusion'])project[name+'.lean']=readFileSync(new URL('./'+name+'.lean',import.meta.url),'utf8')
project['P3TypedClient.lean']=transport
project['P3TypedDefs.lean']=defs
project['BapaProof.lean']=readFileSync(new URL('./P3TypedSource.lean',import.meta.url),'utf8')
project['source-machine.json']=JSON.stringify(source,null,2)+'\n';project['source-laws.json']=JSON.stringify(laws,null,2)+'\n';project['basis.json']=JSON.stringify(basis,null,2)+'\n'
const modules=Object.keys(project).filter(n=>n.endsWith('.lean')&&n!=='lakefile.lean').map(n=>n.slice(0,-5))
project['lakefile.lean']='import Lake\nopen Lake DSL\npackage p3typed\n@[default_target]\nlean_lib P3TypedSource where\n  roots := #['+modules.map(n=>'`'+n).join(', ')+']\n'
mkdirSync(out)
for(const [name,text]of Object.entries(project))writeFileSync(join(out,name),text,{flag:'wx'})
const receipt={schema:'p3-typed-source/v1',status:'EMITTED_NOT_CHECKED',sourceAccepted:false,newSearches:0,inputSha256:sha(capBytes),retainedLeanSha256:sha(raw),sourcePortSha256:sha(readFileSync(new URL('../protocols/ic3syn/models.ts',import.meta.url))),files:Object.fromEntries(Object.entries(project).map(([n,t])=>[n,sha(t)])),sourceTheorem:'bapa_client_server_db_ae_source',parameters:basis.sizes}
writeFileSync(join(out,'EMITTED.json'),JSON.stringify(receipt,null,2)+'\n',{flag:'wx'})
console.log(JSON.stringify(receipt))
