/// <reference types="node" />
// Shape-selected, search-free counted bound erasure and provided-source inclusion.
import type {Machine} from '../../core/machine.ts'
import {boundOf,postName,witnessesOf} from '../../kernel/kernel.ts'
import {retainedCMachineToLean} from '../emit.ts'
import {splitEntryData,type PartOptions} from '../lift/proof-parts.ts'
import type {FamilyBundle} from '../lift/proof-capture.ts'
import {sourceStructure,sourceLeanId,type GenericLiftSource} from '../lift/source.ts'
import {proposeWitnessAlpha} from '../lift/witness-alpha.ts'
import {liftProject,leanSource} from '../lift/project.ts'
import {boundSyntaxValues,candidateBounds,eraseBound,publicCoverage,structuralWeakening,trueCondition,weakeningTerm} from './structural.ts'

/** Supplied by the common hash-bound complete-graph loader. This deliberately
 * does not impose a new outer schema on legacy capsules or rewrite identity. */
export type BoundInclusionBundle={final:Pick<FamilyBundle['final'],'machine'|'laws'|'proof'>,verdict?:{proven:boolean,checked:boolean}}
export type BoundInclusionInput={id:string,bundle:BoundInclusionBundle,providedSourceAST:GenericLiftSource,options:PartOptions}
export type BoundInclusionOutput={
  project:Record<string,string>,familyTheorem:string,sourceTheorems:string[],publicLawIndices:number[],requiredTheorems:string[],bound:number,
  parts:{familySize:number,primaryObligations:number},kind:'bound-inclusion'
}
const eq=(a:unknown,b:unknown)=>sourceStructure(a)===sourceStructure(b)
function eligible(m:Machine):void {
  if(m.history||Object.keys(m.sums??{}).length||Object.keys(m.fns??{}).length||Object.keys(m.leasts??{}).length)throw Error('unsupported bound-inclusion machine extension')
}
function operational(m:Machine):Machine {
  // Parameter labels only allocate the shared variable basis; SMachine has no
  // params field. Preserve their actual uses in all emitted expressions.
  return {...m,name:'',params:[],counts:undefined,pre:undefined,assume:undefined,maps:m.maps??{},inputMaps:m.inputMaps??[],
    step:{...m.step,state:m.step.state??{},maps:m.step.maps??{},flags:m.step.flags??{}}}
}
/** Call only after complete-graph validation and exact one-time term restoration.
 * Null means no bound-erasure candidate. A candidate that is unsupported or
 * ambiguous throws; callers MUST NOT turn that failure into strategy fallback.
 * Emission is not checking: every returned theorem requires native Lean. */
export function tryEmitBoundInclusion(input:BoundInclusionInput):BoundInclusionOutput|null {
  const {id,bundle,providedSourceAST:source,options}=input
  if(id!==sourceLeanId(source.id)||!/^bapa_[A-Za-z0-9_]+$/.test(id))throw Error('unsafe or inconsistent full Lean prefix')
  if(source.schema!=='gdp-lift-source/v1')throw Error('invalid provided source ABI')
  sourceStructure(source)
  const f=bundle.final
  if(!f?.machine||!f.laws||!f.proof)return null
  const bounds=candidateBounds(source.machine,f.machine)
  if(!bounds.length){
    if(!eq(source.machine.pre??trueCondition,f.machine.pre??trueCondition)&&boundSyntaxValues(f.machine.pre??trueCondition).length)throw Error('unsupported bound-erasure precondition')
    return null
  }
  if(bounds.length!==1)throw Error('ambiguous bound-erasure candidate')
  const bound=bounds[0]!
  if(bundle.verdict&&(!bundle.verdict.proven||!bundle.verdict.checked))throw Error('unverified complete family')
  eligible(source.machine);eligible(f.machine)
  if(!Object.keys(f.machine.counts??{}).length)throw Error('bound inclusion requires counted family')
  if(!f.laws.length||new Set(f.laws.map(l=>l.name)).size!==f.laws.length)throw Error('empty or ambiguous retained family')
  const expected=f.laws.flatMap(l=>[l.name+' @start',l.name+' @step'])
  if(expected.some(k=>!Object.hasOwn(f.proof.certs,k))||Object.keys(f.proof.certs).some(k=>!expected.includes(k)))throw Error('incomplete or unrepresented retained family certificates')
  const producer=eraseBound(f.machine,bound),coverage=publicCoverage(source.laws,f.laws,bound)
  const pre=structuralWeakening(source.machine.pre??trueCondition,producer.pre??trueCondition)
  const admission=structuralWeakening(source.machine.assume??trueCondition,producer.assume??trueCondition)
  if(!pre||!admission)throw Error('unsupported structural source admission')
  // Only exact operations, local quantified/row alpha, and extra count maps are
  // supported. The corresponding equalities and capture avoidance are checked
  // independently in emitted Lean; this preflight is not a semantic assertion.
  const alpha=proposeWitnessAlpha(operational(source.machine),operational(producer))
  const rs=alpha?.renames??[],rows=alpha?.rows??[]
  for(const [name,d]of Object.entries(source.machine.counts??{}))if(!eq(d,producer.counts?.[name]))throw Error('unsupported source count change: '+name)
  for(const n of [options.maxOutputBytes,options.maxFiles,options.heartbeats,options.recursionDepth])if(!Number.isSafeInteger(n)||n<1)throw Error('finite positive generator limits required')
  const vars=new Set<string>([...source.machine.params,...source.machine.inputs,...Object.keys(source.machine.state),...Object.keys(source.machine.step.state??{})])
  const maps=new Set<string>([...Object.keys(source.machine.maps??{}),...Object.keys(source.machine.step.maps??{}),...(source.machine.inputMaps??[])])
  const visit=(x:unknown):void=>{
    if(!x||typeof x!=='object')return
    if(Array.isArray(x)){x.forEach(visit);return}
    const o=x as Record<string,unknown>
    if(o.op==='var')vars.add(o.name as string)
    if(o.op==='get')maps.add(o.map as string)
    Object.values(o).forEach(visit)
  }
  visit(source.machine);visit(source.laws)
  for(const [name,q]of Object.entries(source.machine.step.flags??{})){
    vars.add('?'+name)
    if(q.op==='all'){boundOf(q).forEach(x=>vars.add(x));witnessesOf(name,q).forEach(x=>vars.add(x))}
  }
  for(const w of Object.values(source.machine.step.maps??{}))if('each'in w)vars.add(w.each)
  for(const l of [...source.laws,...(source.machine.facts??[])]){if(l.forall)vars.add(l.forall);l.keys?.forEach(x=>vars.add(x))}
  for(const [name,d]of Object.entries(source.machine.counts??{})){
    maps.add(name);maps.add(postName(name));vars.add(d.j);vars.add(d.key);vars.add(d.lo??d.j)
  }
  for(const r of rs){vars.add('?'+r.flag);vars.add(r.old);vars.add(r.fresh)}
  for(const r of rows){vars.add(r.old);vars.add(r.fresh);maps.add(r.map)}
  let sourceDefs=''
  const raw=id+'_retained'
  // Regenerate ALL retained entries from the capsule, not a frozen Proofs file.
  // retainedCMachineToLean validates native certificate data without any search.
  const text=retainedCMachineToLean(raw,f.machine,f.laws,f.proof,{extraVars:[...vars],extraMaps:[...maps],after:b=>{
    const m=source.machine,counts=Object.entries(m.counts??{}),normal={...m,counts:undefined,inputMaps:[...(m.inputMaps??[]),...counts.map(([n])=>n)]}
    sourceDefs=`def ${id}_source : SMachine := ${b.machine(normal)}
def ${id}_source_decls : List CDecl := ${b.decls(m.counts)}
def ${id}_source_renames : List QAlpha.Rename := [${rs.map(r=>`⟨${b.ix('?'+r.flag)}, ${b.ix(r.old)}, ${b.ix(r.fresh)}⟩`).join(', ')}]
def ${id}_source_row_renames : List RowAlpha.Rename := [${rows.map(r=>`⟨${b.mx(r.map)}, ${b.ix(r.old)}, ${b.ix(r.fresh)}⟩`).join(', ')}]
def ${id}_fresh : List Nat := [${Object.keys(f.machine.counts??{}).filter(n=>!Object.hasOwn(m.counts??{},n)).map(b.mx).join(', ')}]
${source.laws.map((l,j)=>`def ${id}_source_law${j} : MLaw := ⟨${b.condition(l.holds)}, ${l.forall?`some ${b.ix(l.forall)}`:'none'}⟩\ndef ${id}_source_keys${j} : List Nat := [${(l.keys??[]).map(b.ix).join(', ')}]`).join('\n')}`
    return ''
  }})
  const match=new RegExp(`\\n(?:noncomputable )?def ${raw}_proof : List (CEntryF|CEntry) := `).exec(text),check=text.indexOf(`\ntheorem ${raw}_check :`)
  if(!match||check<0)throw Error('unsupported retained emission layout')
  const entries=splitEntryData(text.slice(match.index+match[0].length,check))
  if(entries.length!==f.laws.length)throw Error('lost retained family entry')
  const entryType=match[1]!,hasAlpha=text.includes(`def ${raw}_checkedMachine :`)
  const header=(imports:string[])=>imports.map(s=>'import '+s).join('\n')+`\nopen Kern Cert\nset_option maxHeartbeats ${options.heartbeats}\nset_option maxRecDepth ${options.recursionDepth}\n`
  const names=entries.map((_,j)=>id+'_entry'+j)
  let definitions=text.slice(0,match.index)+'\n'
  definitions+=`def ${id}_bound : Nat := ${bound}
def ${id}_machine : SMachine := Bapa.CertificateBoundErasure.machine ${id}_bound ${raw}_machine
def ${id}_decls : List CDecl := ${raw}_decls.map (Bapa.CertificateBoundErasure.countDeclaration ${id}_bound)
`
  definitions+=entries.map((e,j)=>`noncomputable def ${names[j]}_raw : ${entryType} := ${e}\nnoncomputable def ${names[j]} : CEntryF := Bapa.StructuralWeakening.countedEntryF ${id}_bound (${names[j]}_raw${entryType==='CEntry'?'.toF':''})`).join('\n')
  definitions+=`\nnoncomputable def ${id}_family : List CEntryF := [${names.join(', ')}]\n${sourceDefs}\n`
  const checked=hasAlpha?id+'_checkedMachine':id+'_machine'
  if(hasAlpha)definitions+=`def ${checked} : SMachine := QAlpha.renameAll ${id}_machine ${raw}_renames\n`
  const project=liftProject(definitions,{name:'BapaProof'}),defsModule=id+'_Defs'
  for(const n of ['CertificateBoundErasure','CountedSourceProjection','CountedNoninterference','CountedSourceBridge','SourceInclusion'])project[n+'.lean']=leanSource(n)
  project['StructuralWeakening.lean']=leanSource('StructuralWeakening')
  project[defsModule+'.lean']=header(['QAlpha','RowAlpha','StructuralWeakening'])+definitions
  const requiredTheorems:string[]=[]
  const printTheorem=(name:string)=>{requiredTheorems.push(name);return '\n#print axioms '+name+'\n'}
  const entryModules=names.map((name,j)=>{
    const module=id+'_Entry'+j,thm=name+'_check'
    project[module+'.lean']=header([defsModule])+`theorem ${thm} : cEntryCheckF ${checked} ${id}_decls (${id}_family.map (·.e)) ${name} = true := by decide +kernel\n`+printTheorem(thm)
    return module
  })
  const global=id+'_global',family=id+'_laws'
  let familyBody=`theorem ${global} : cGlobalOkF ${checked} ${id}_decls (${id}_family.map (·.e)) = true := by decide +kernel
 theorem ${id}_check : checkCMachineF ${checked} ${id}_decls ${id}_family = true := by
  apply checkCMachineF_of_parts _ _ _ ${global}
  intro ce hce
  simp only [${id}_family, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hce
  rcases hce with ${names.map(()=> 'rfl').join(' | ')}
${names.map(n=>'  · exact '+n+'_check').join('\n')}
 theorem ${family} : ∀ ρ M, CReach ${id}_machine ${id}_decls ρ M → ∀ e ∈ ${id}_family, e.e.Holds ρ (withCnt ${id}_decls ρ M) :=
  ${hasAlpha?`QAlpha.cmachineF_sound ${id}_machine ${raw}_renames ${id}_decls ${id}_family (by decide +kernel) ${id}_check`:`cmachineF_sound ${id}_machine ${id}_decls ${id}_family ${id}_check`}
`
  const transported=id+'_transported_laws'
  familyBody+=`theorem ${transported} : ∀ ρ M, CReach ${id}_machine ${id}_decls ρ M → ∀ e ∈ ${id}_family, e.e.Holds ρ (withCnt ${id}_decls ρ M) := ${family}\n`
  familyBody+=printTheorem(global)+printTheorem(id+'_check')+printTheorem(family)+printTheorem(transported)
  project[id+'_Family.lean']=header([defsModule,...entryModules])+familyBody
  const sourceTheorems=source.laws.map((_,j)=>id+'_source_law'+j+'_holds')
  // Finite declaration membership is constructor elimination, not DecidableEq
  // over CDecl (which has no such instance). No fixed number of declarations.
  const membership=(list:string,count:number,publicCase:boolean)=>`by
      intro d hd${publicCase?' hn':''}
      simp only [${list}, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
      ${count?`rcases hd with ${Array(count).fill('rfl').join(' | ')}\n      all_goals simp_all [${id}_source_decls, ${id}_decls, ${raw}_decls, ${id}_fresh, ${id}_bound, Bapa.CertificateBoundErasure.countDeclaration, Bapa.CertificateBoundErasure.expr, Bapa.CertificateBoundErasure.condition]`:'cases hd'}`
  const sourceMem=membership(id+'_source_decls',Object.keys(source.machine.counts??{}).length,false)
  const publicMem=membership(`${id}_decls, ${raw}_decls, List.map_cons, List.map_nil`,Object.keys(f.machine.counts??{}).length,true)
  let body=`def ${id}_source_qalpha : SMachine := QAlpha.renameAll ${id}_source ${id}_source_renames
def ${id}_source_alpha : SMachine := RowAlpha.renameAll ${id}_source_qalpha ${id}_source_row_renames
def ${id}_source_plus : SMachine := {${id}_source_alpha with carried := ${id}_source_alpha.carried ++ ${id}_fresh}
theorem ${id}_alpha_valid : QAlpha.validAll ${id}_source ${id}_source_renames = true := by decide +kernel
theorem ${id}_row_valid : RowAlpha.validAll ${id}_source_qalpha ${id}_source_row_renames = true := by decide +kernel
theorem ${id}_view (ρ M ι κ) : sView ${id}_source_plus ρ M ι κ = sView ${id}_machine ρ M ι κ := by rfl
theorem ${id}_next (ρ M ι κ) : sNext ${id}_source_plus ρ M ι κ = sNext ${id}_machine ρ M ι κ := by rfl
theorem ${id}_pre : Bapa.StructuralWeakening.Subsumes ${id}_source_plus.f.m.pre ${id}_machine.f.m.pre := ${weakeningTerm(pre)}
theorem ${id}_admission : Bapa.StructuralWeakening.Subsumes ${id}_source_plus.f.m.assume ${id}_machine.f.m.assume := ${weakeningTerm(admission)}
theorem ${id}_inclusion : SourceInclusion ${id}_source_plus ${id}_machine where
  inputs := by rfl
  carried := by rfl
  initial := by rfl
  startMaps := by intro M h; exact h
  pre := Bapa.StructuralWeakening.sound ${id}_pre
  facts := by intro ρ M h; exact h
  pfacts := by intro ρ M h; exact h
  admission := by
    intro ρ M ι κ h
    rw [${id}_view] at h
    exact Bapa.StructuralWeakening.sound ${id}_admission _ _ h
  next := by intro ρ M ι κ _; exact ${id}_next ρ M ι κ
`
  coverage.indices.forEach((k,j)=>{
    const entry=names[k]!,weak=id+'_weak'+j,lawImp=id+'_law_implication'+j
    body+=`noncomputable def ${weak} : SEntry := {${entry}.e with law := ${id}_source_law${j}, keys2 := ${id}_source_keys${j}}
theorem ${lawImp} : SourceLawImplication ${entry}.e ${weak} :=
  Bapa.StructuralWeakening.law (by rfl) (by rfl) (${weakeningTerm(coverage.proofs[j]!)})
theorem ${sourceTheorems[j]} (ρ M) (hr : CReach ${id}_source ${id}_source_decls ρ M) :
    holdsOver ${id}_source_law${j} (withCnt ${id}_source_decls ρ M) ${id}_source_keys${j} ρ := by
  have hq := (QAlpha.renameAll_equiv ${id}_source ${id}_source_renames ${id}_alpha_valid).symm.creach_imp ${id}_source_decls hr
  have ha : CReach ${id}_source_alpha ${id}_source_decls ρ M :=
    (RowAlpha.renameAll_equiv ${id}_source_qalpha ${id}_source_row_renames ${id}_row_valid).symm.creach_imp ${id}_source_decls hq
  have h := bapa_counted_source_law ${id}_source_alpha ${id}_source_decls ${id}_decls ${id}_fresh ${id}_fresh ${entry}.e
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (${sourceMem}) (${publicMem}) (stepAvoids_of_check _ _ (by decide +kernel))
    (by decide +kernel)
    (by
      intro X N hh
      exact ${family} X N (${id}_inclusion.creach ${id}_decls hh) ${entry} (by simp [${id}_family])) ρ M ha
  exact ${lawImp} ρ _ h
`
    body+=printTheorem(lawImp)+printTheorem(sourceTheorems[j]!)
  })
  for(const t of [id+'_alpha_valid',id+'_row_valid',id+'_pre',id+'_admission',id+'_inclusion'])body+=printTheorem(t)
  project['BapaProof.lean']=header([id+'_Family','StructuralWeakening','RowAlpha'])+body
  const modules=Object.keys(project).filter(n=>n.endsWith('.lean')&&n!=='lakefile.lean').map(n=>n.slice(0,-5))
  project['lakefile.lean']='import Lake\nopen Lake DSL\npackage boundinclusion\n@[default_target]\nlean_lib BoundInclusion where\n  roots := #['+modules.map(n=>'`'+n).join(', ')+']\n'
  if(Object.keys(project).length>options.maxFiles||Object.values(project).reduce((n,s)=>n+Buffer.byteLength(s),0)>options.maxOutputBytes)throw Error('complete bound-inclusion project exceeds output budget')
  return {project,familyTheorem:transported,sourceTheorems,publicLawIndices:coverage.indices,requiredTheorems,bound,kind:'bound-inclusion',parts:{familySize:entries.length,primaryObligations:2*entries.length}}
}
