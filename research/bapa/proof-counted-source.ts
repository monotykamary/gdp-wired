// No-search counted source project. Every proposed correspondence is checked in Lean.
import {readFileSync,mkdirSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {leanProject} from '../../lean-kernel/emit.ts'
import type {FamilyBundle,NativeBundle} from './proof-capture.ts'
import {countedSourceDefinitions} from './counted-source-data.ts'
import {emitCountedParts,type PartOptions} from './proof-parts.ts'
import {readFamilyCapsule} from './proof-codec.ts'
import {restoreTermPrelude} from './proof-prelude.ts'
export function countedSourceProject(id:string,input:NativeBundle,options:PartOptions){
  if(input.route!=='counted-family')throw Error('counted source projection needs a complete counted family')
  const bundle:FamilyBundle=input,data=countedSourceDefinitions(id,bundle),parts=emitCountedParts(id,bundle,options)
  const sourceTheorems=data.publicLawIndices.map((_,j)=>`${id}_source_law${j}_holds`)
  // CDecl deliberately has no DecidableEq instance. Eliminate finite membership
  // hypotheses by constructors rather than asking decide to compare declarations.
  const membershipCases=(list:string,count:number,rest:string)=>`by\n      intro d hd${rest.startsWith('PUBLIC:')?' hn':''}\n      simp only [${list}, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd\n      ${count?`rcases hd with ${Array(count).fill('rfl').join(' | ')}\n      all_goals ${rest.replace('PUBLIC:','')}`:''}`
  const sourceMembership=membershipCases(id+'_source_decls',Object.keys(bundle.original.machine.counts??{}).length,`simp [${id}_decls]`)
  const publicMembership=membershipCases(id+'_decls',Object.keys(bundle.final.machine.counts??{}).length,`PUBLIC:simp_all [${id}_source_count_maps, ${id}_source_decls]`)
  const publicProofs=data.publicLawIndices.map((k,j)=>{
    const entry=`${id}_entry${k}`
    return `theorem ${id}_source_law${j}_eq : ${id}_source_law${j} = ${entry}.e.law := by rfl
theorem ${id}_source_keys${j}_eq : ${id}_source_keys${j} = ${entry}.e.keys2 := by rfl
theorem ${id}_source_law${j}_holds (ρ M) (hr : CReach ${id}_source ${id}_source_decls ρ M) :
    holdsOver ${id}_source_law${j} (withCnt ${id}_source_decls ρ M) ${id}_source_keys${j} ρ := by
  have hr' : CReach ${id}_source_alpha ${id}_source_decls ρ M :=
    (QAlpha.renameAll_equiv ${id}_source ${id}_source_renames ${id}_source_alpha_valid).symm.creach_imp ${id}_source_decls hr
  have h := bapa_counted_source_law ${id}_source_alpha ${id}_source_decls ${id}_decls
    ${id}_source_count_maps ${id}_source_count_maps ${entry}.e
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (${sourceMembership}) (${publicMembership}) (stepAvoids_of_check _ _ (by decide +kernel))
    (by decide +kernel)
    (by
      intro X N hreach
      rw [${id}_source_shape] at hreach
      exact ${id}_laws X N hreach ${entry} (by simp [${id}_family])) ρ M hr'
  simpa only [SEntry.Holds, ${id}_source_law${j}_eq, ${id}_source_keys${j}_eq] using h
#print axioms ${id}_source_law${j}_holds`
  }).join('\n')
  const body=`import CountedSourceBridge
import ${parts.finalModule}
open Kern Cert
set_option maxHeartbeats ${options.heartbeats}
set_option maxRecDepth ${options.recursionDepth}
${data.sourceDefs}
def ${id}_source_alpha : SMachine := QAlpha.renameAll ${id}_source ${id}_source_renames
theorem ${id}_source_alpha_valid : QAlpha.validAll ${id}_source ${id}_source_renames = true := by decide +kernel
theorem ${id}_source_shape : {${id}_source_alpha with carried := ${id}_source_alpha.carried ++ ${id}_source_count_maps} = ${id}_machine := by rfl
${publicProofs}
#print axioms ${id}_laws
#print axioms ${id}_source_alpha_valid
#print axioms ${id}_source_shape
`
  if(/\b(?:sorry|axiom|native_decide)\b/.test(body))throw Error('unapproved counted source construct')
  const defs=parts.files.find(f=>f.role==='definitions')
  if(!defs)throw Error('split definitions missing')
  const project=leanProject(defs.text,{name:'BapaProof'})
  for(const f of parts.files)project[f.module+'.lean']=f.text
  for(const name of ['FamilyParts','CountedSourceProjection','CountedNoninterference','CountedSourceBridge'])
    project[name+'.lean']=readFileSync(new URL('./'+name+'.lean',import.meta.url),'utf8')
  project['BapaProof.lean']=body
  const modules=Object.keys(project).filter(n=>n.endsWith('.lean')&&n!=='lakefile.lean').map(n=>n.slice(0,-5))
  project['lakefile.lean']='import Lake\nopen Lake DSL\npackage bapasource\n@[default_target]\nlean_lib BapaSource where\n  roots := #['+modules.map(n=>'`'+n).join(', ')+']\n'
  return {project,sourceTheorems,publicLawIndices:data.publicLawIndices,parts:{familySize:parts.familySize,primaryObligations:parts.primaryObligations,frontiers:parts.frontiers}}
}

if(import.meta.main){
  const args=process.argv.slice(2),v:Record<string,string>={},keys=new Set(['--capture','--sha256','--out','--weight-limit'])
  for(let i=0;i<args.length;i+=2){const k=args[i]!,value=args[i+1];if(!keys.has(k)||v[k]!==undefined||!value||value.startsWith('--'))throw Error('expected --capture DIR --sha256 HASH --out NEW_DIR [--weight-limit N]');v[k]=value}
  if(!v['--capture']||!v['--sha256']||!v['--out'])throw Error('capture, SHA-256 and new output directory required')
  const metadata:[object,unknown][]=[]
  const {manifest,data}=readFamilyCapsule(v['--capture'],v['--sha256'],{maxBytes:512*1024*1024,maxNodes:4000000,maxStrings:200000,maxArrayLength:2000000,maxShards:2048},(o,m)=>metadata.push([o,m]))
  const bundle=data as NativeBundle
  restoreTermPrelude(bundle.terms,metadata)
  const id='bapa_'+bundle.identity.protocol.replace(/[^A-Za-z0-9_]/g,'_')
  const emitted=countedSourceProject(id,bundle,{weightLimit:BigInt(v['--weight-limit']??1000000),maxOutputBytes:256*1024*1024,maxFiles:20000,heartbeats:200000000,recursionDepth:100000})
  const hashes=Object.fromEntries(Object.entries(emitted.project).map(([name,text])=>[name,createHash('sha256').update(text).digest('hex')]))
  mkdirSync(v['--out'])
  for(const [name,text]of Object.entries(emitted.project))writeFileSync(join(v['--out'],name),text,{flag:'wx'})
  const receipt={schema:'bapa-emission/v1',status:'EMITTED_NOT_CHECKED',inputSha256:v['--sha256'],identity:manifest.identity,route:bundle.route,projection:manifest.projection,familyTheorem:id+'_laws',files:hashes,leanVersion:'4.34.0',leanExecuted:false,allSizesProven:false,sourceProjection:{kind:'counted',status:'EMITTED_NOT_CHECKED',sourceTheorems:emitted.sourceTheorems,publicLawIndices:emitted.publicLawIndices,publicLawNames:bundle.original.laws.map(l=>l.name)},parts:emitted.parts,publicSourceAcceptance:'REQUIRES_LEAN_SOURCE_PROJECTION_CHECK'}
  writeFileSync(join(v['--out'],'EMITTED.json'),JSON.stringify(receipt,null,2)+'\n',{flag:'wx'})
  console.log(JSON.stringify(receipt))
}
