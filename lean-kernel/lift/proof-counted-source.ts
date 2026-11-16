// No-search counted source project. Every proposed correspondence is checked in Lean.
import type {FamilyBundle,NativeBundle} from './proof-capture.ts'
import {countedSourceDefinitions} from './counted-source-data.ts'
import {emitCountedParts,type PartOptions} from './proof-parts.ts'
import {leanSource,liftProject as leanProject} from './project.ts'
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
  have hq := (QAlpha.renameAll_equiv ${id}_source ${id}_source_renames ${id}_source_alpha_valid).symm.creach_imp ${id}_source_decls hr
  have hr' : CReach ${id}_source_alpha ${id}_source_decls ρ M :=
    (RowAlpha.renameAll_equiv ${id}_source_qalpha ${id}_source_row_renames ${id}_source_row_valid).symm.creach_imp ${id}_source_decls hq
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
  const body=`import RowAlpha
import CountedSourceBridge
import ${parts.finalModule}
open Kern Cert
set_option maxHeartbeats ${options.heartbeats}
set_option maxRecDepth ${options.recursionDepth}
${data.sourceDefs}
def ${id}_source_qalpha : SMachine := QAlpha.renameAll ${id}_source ${id}_source_renames
def ${id}_source_alpha : SMachine := RowAlpha.renameAll ${id}_source_qalpha ${id}_source_row_renames
theorem ${id}_source_alpha_valid : QAlpha.validAll ${id}_source ${id}_source_renames = true := by decide +kernel
theorem ${id}_source_row_valid : RowAlpha.validAll ${id}_source_qalpha ${id}_source_row_renames = true := by decide +kernel
theorem ${id}_source_shape : {${id}_source_alpha with carried := ${id}_source_alpha.carried ++ ${id}_source_count_maps} = ${id}_machine := by rfl
${publicProofs}
#print axioms ${id}_laws
#print axioms ${id}_source_alpha_valid
#print axioms ${id}_source_row_valid
#print axioms ${id}_source_shape
`
  if(/\b(?:sorry|axiom|native_decide)\b/.test(body))throw Error('unapproved counted source construct')
  const defs=parts.files.find(f=>f.role==='definitions')
  if(!defs)throw Error('split definitions missing')
  const project=leanProject(defs.text,{name:'BapaProof'})
  for(const f of parts.files)project[f.module+'.lean']=f.text
  for(const name of ['FamilyParts','CountedSourceProjection','CountedNoninterference','CountedSourceBridge'])
    project[name+'.lean']=leanSource(name)
  project['BapaProof.lean']=body
  const modules=Object.keys(project).filter(n=>n.endsWith('.lean')&&n!=='lakefile.lean').map(n=>n.slice(0,-5))
  project['lakefile.lean']='import Lake\nopen Lake DSL\npackage bapasource\n@[default_target]\nlean_lib BapaSource where\n  roots := #['+modules.map(n=>'`'+n).join(', ')+']\n'
  return {project,sourceTheorems,publicLawIndices:data.publicLawIndices,parts:{familySize:parts.familySize,primaryObligations:parts.primaryObligations,frontiers:parts.frontiers}}
}
