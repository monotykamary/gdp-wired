import type {Machine,Law,E} from '../../core/machine.ts'
import type {ProofOutputNode} from '../../core/proof-output.ts'
import {boundOf,witnessesOf,substC} from '../../kernel/kernel.ts'
import {retainedSMachineToLean} from '../emit.ts'
import {liftProject} from '../lift/project.ts'
import type {GenericLiftSource} from '../lift/source.ts'
import {sourceStructure} from '../lift/source.ts'
import type {PartOptions} from '../lift/proof-parts.ts'
import {proposeWitnessAlpha} from '../lift/witness-alpha.ts'
import {deriveTypedRoles,type Roles} from './roles.ts'
import {associativeShape} from './shape.ts'

export type TypedBoundBundle={original:{machine:Machine,laws:Law[]},proof?:ProofOutputNode,verdict:{proven:boolean,checked:boolean},final?:unknown}
export type TypedBoundOptions={id:string,bundle:TypedBoundBundle,providedSourceAST:GenericLiftSource,options:PartOptions}
export type TypedBoundEmission={project:Record<string,string>,familyTheorem:string,sourceTheorems:string[],publicLawIndices:number[],requiredTheorems:string[],roles:Roles,status:'EMITTED_NOT_CHECKED'}
const list=(xs:(string|number)[])=>'['+xs.join(', ')+']'
const equal=(a:unknown,b:unknown)=>sourceStructure(a)===sourceStructure(b)
const walk=(x:any,f:(x:any)=>void):void=>{if(!x||typeof x!=='object')return;f(x);Object.values(x).forEach(v=>Array.isArray(v)?v.forEach(y=>walk(y,f)):walk(v,f))}
const transform=(x:any,r:Roles,scope:Record<string,string>):any=>{
 if(!x||typeof x!=='object')return x
 if(Array.isArray(x))return x.map(v=>transform(v,r,scope))
 if((x.op==='<'||x.op==='<=')&&x.b?.op==='const'&&x.b.value===r.bound){const p=x.a.op==='var'?scope[x.a.name]:x.a.op==='get'?r.values[x.a.map]:undefined;if(!p)throw Error('unclassified typed bound: '+JSON.stringify(x.a));return {...x,a:transform(x.a,r,scope),b:{op:'var',name:p}}}
 return Object.fromEntries(Object.entries(x).map(([k,v])=>[k,transform(v,r,scope)]))
}
const normalized=(m:Machine):Machine=>{const {relations:_r,name:_n,...rest}=m;return associativeShape({...rest,name:'source',maps:m.maps??{},step:{...m.step,maps:m.step.maps??{}}})}

/** After caller-owned capsule/hash validation and single term restoration.
 * No protocol lookup, search, old generated Lean, or schema rewriting occurs. */
export function tryTypedBoundSubstitution({id,bundle,providedSourceAST:source,options}:TypedBoundOptions):TypedBoundEmission|null {
 if(!/^[A-Za-z][A-Za-z0-9_]*$/.test(id)||id.length>80)throw Error('unsafe typed Lean identifier')
 if(source.schema!=='gdp-lift-source/v1'||!source.laws.length)throw Error('invalid typed source envelope')
 sourceStructure(source)
 for(const n of [options.maxOutputBytes,options.maxFiles,options.recursionDepth])if(!Number.isSafeInteger(n)||n<1)throw Error('positive finite typed output limits required')
 if(!Number.isSafeInteger(options.heartbeats)||options.heartbeats<0)throw Error('invalid typed heartbeat budget')
 // A counted or non-parametric family is not this route. A recognized typed
 // candidate is never silently delegated after encountering an unsupported mix.
 if(!bundle.proof)return null
 let probe=false;walk(source.machine,x=>{if((x.op==='<'||x.op==='<=')&&x.b?.op==='var'&&source.machine.params.includes(x.b.name))probe=true})
 if(!probe)return null
 if(!bundle.verdict?.proven||!bundle.verdict.checked)throw Error('unverified typed candidate')
 let node=bundle.proof;let context:any;const seen=new Set<ProofOutputNode>()
 while(node.kind==='derived'){
  if(seen.has(node)||node.parents.length!==1||!node.parents[0])throw Error('typed candidate needs a unique complete producer path');seen.add(node)
  const c=node.context as any
  if(c?.kind==='skolem'){if(context)throw Error('mixed typed witness contexts');context=c}
  else if(!['projection','inference'].includes(c?.kind))throw Error('unsupported typed provenance context')
  node=node.parents[0]
 }
 if(node.kind!=='usual')throw Error('unsupported typed/count mixing')
 const leaf=node
 for(const m of [source.machine,bundle.original.machine,leaf.machine])if(m.history||Object.keys(m.counts??{}).length||Object.keys(m.sums??{}).length||Object.keys(m.fns??{}).length||m.facts?.length)throw Error('unsupported typed machine extension')
 const roles=deriveTypedRoles(source,bundle.original,leaf.machine,leaf.laws)
 if(!roles)return null
 if(!context||!context.G||!context.plains)throw Error('typed witness context with explicit substitution required')
 const gm=context.G as {orig:Machine,vars:Record<string,{start:E,step:E}>,maps:Record<string,{start:number,write:any}>}
 if(!equal(normalized(gm.orig),normalized(context.original)))throw Error('typed context source mismatch')
 const typed=transform(leaf.machine,roles,roles.base) as Machine
 // The context's source can have a different fresh quantified binder than
 // its retained producer. Project the actual producer's ghost fields by the
 // declared context sets; Lean rechecks this projection against the supplied
 // source through alpha validity, ghost validity and operational inclusion.
 const strip=<T>(r:Record<string,T>|undefined,ghosts:Record<string,unknown>):Record<string,T>=>Object.fromEntries(Object.entries(r??{}).filter(([name])=>!Object.hasOwn(ghosts,name)))
 const bare:Machine={...leaf.machine,state:strip(leaf.machine.state,gm.vars),maps:strip(leaf.machine.maps,gm.maps),step:{...leaf.machine.step,state:strip(leaf.machine.step.state,gm.vars),maps:strip(leaf.machine.step.maps,gm.maps)}}
 const typedOriginal=transform(bare,roles,roles.base) as Machine
 // Alpha proposal only; Lean validates the actual provided machine, not this
 // finite shadow or a copied public-source assertion.
 const alpha=proposeWitnessAlpha(normalized(source.machine),normalized({...typedOriginal,params:source.machine.params}))
 const publicLawIndices:number[]=[],substitutions:Record<string,E>[]=[]
 for(let j=0;j<source.laws.length;j++){
  const l=source.laws[j]!,old=bundle.original.laws[j]
  if(!old||!l.some?.length||l.ex||l.stated||l.finite||l.witness)throw Error('unsupported typed public law (explicit existential only)')
  if(l.forall!==old.forall||!equal(l.keys??[],old.keys??[]))throw Error('typed universal-binder alpha requires a separate bridge')
  if(!old.some||old.some.length!==l.some.length||new Set(old.some).size!==old.some.length||new Set(l.some).size!==l.some.length)throw Error('ambiguous typed existential binder correspondence')
  const q=context.plains[old.name]
  if(!q||!q.sub)throw Error('missing typed witness substitution')
  const matches=leaf.laws.flatMap((f,i)=>equal(f,q.plain)?[i]:[])
  if(matches.length!==1)throw Error('missing/ambiguous typed public family correspondence')
  const i=matches[0]!;publicLawIndices.push(i)
  if(Object.keys(q.sub).length!==old.some.length||!old.some.every(k=>Object.hasOwn(q.sub,k)))throw Error('incomplete typed existential substitution')
  const publicSub=Object.fromEntries(l.some.map((k,j)=>[k,q.sub[old.some![j]!]]))
  substitutions.push(publicSub)
  // The source differs from its captured public statement only through checked
  // finite-bound substitution. Its full provided literal is emitted below.
  const renamed=substC(old.holds,{vars:Object.fromEntries(old.some.map((k,j)=>[k,{op:'var' as const,name:l.some![j]!}])),maps:{},flags:{}})
  const body=transform(renamed,roles,roles.publicScopes[j]!)
  if(!equal(associativeShape(body),associativeShape(l.holds)))throw Error('provided typed source law differs beyond inferred bound substitution')
 }
 const free=new Set<string>([...source.machine.params,...source.machine.inputs,...Object.keys(source.machine.state)])
 walk([source,typed],x=>{if(x.op==='var')free.add(x.name)})
 for(const [f,q]of Object.entries(leaf.machine.step.flags??{}))if(q.op==='all'){free.add('?'+f);boundOf(q).forEach(k=>free.add(k));witnessesOf(f,q).forEach(k=>free.add(k))}
 source.laws.forEach(l=>[l.forall,...(l.keys??[]),...(l.some??[])].forEach(k=>{if(k)free.add(k)}))
 alpha?.renames.forEach(r=>{free.add(r.old);free.add(r.fresh)});alpha?.rows.forEach(r=>{free.add(r.old);free.add(r.fresh)})
 const raw=id+'_retained',sourceTheorems=source.laws.map((_,j)=>id+'_source_law'+j+'_holds'),familyTheorem=id+'_laws'
 let extra=''
 const emitted=retainedSMachineToLean(raw,leaf.machine,leaf.laws,leaf.proof,{free:[...free],after:(ix,mx,lit,c)=>{
  const typing=(s:Record<string,string>)=>`⟨${list(roles.sizes.map(ix))}, ${list(Object.entries(s).map(([v,p])=>`(${ix(v)}, ${ix(p)})`))}, ${list(Object.entries(roles.values).map(([m,p])=>`(${mx(m)}, ${ix(p)})`))}⟩`
  const renames=list((alpha?.renames??[]).map(r=>`⟨${ix('?'+r.flag)}, ${ix(r.old)}, ${ix(r.fresh)}⟩`))
  const rows=list((alpha?.rows??[]).map(r=>`⟨${mx(r.map)}, ${ix(r.old)}, ${ix(r.fresh)}⟩`))
  const ghostVars=Object.keys(gm.vars),ghostMaps=Object.keys(gm.maps)
  function expr(e:E):string {
   switch(e.op){
    case 'var': return `.var ${ix(e.name)}`
    case 'const': if(!Number.isSafeInteger(e.value)||e.value<0)throw Error('unsupported natural literal');return `.const ${e.value}`
    case 'get': return `.get ${mx(e.map)} (${expr(e.key)})`
    case 'if': return `.ite (${c(e.c)}) (${expr(e.then)}) (${expr(e.else)})`
    case 'mul': return `.mul ${e.k} (${expr(e.a)})`
    case 'proj': return `.proj ${e.k} (${expr(e.a)})`
    case 'add': case 'max': case 'min': case 'prod': case 'sub': case 'tup':
      return `.${e.op} (${expr(e.a)}) (${expr(e.b)})`
   }
  }
  const ghostScalars=list(ghostVars.map(v=>`(${ix(v)}, ${expr(gm.vars[v]!.start)}, ${expr(transform(gm.vars[v]!.step,roles,roles.base))})`))
  const ghostStarts=list(ghostMaps.map(m=>`(${mx(m)}, ${gm.maps[m]!.start})`))
  const ghostWrites=list(ghostMaps.map(m=>{const w=gm.maps[m]!.write;if('each'in w)throw Error('typed ghost row update unsupported');return `(${mx(m)}, ${expr(w.key)}, ${expr(transform(w.value,roles,roles.base))})`}))
  const body=source.laws.map((l,j)=>{
   const i=publicLawIndices[j]!,p=id+'_public'+j,sub=substitutions[j]!,sigma=list(l.some!.map(k=>`(${ix(k)}, ${expr(sub[k]!)})`))
   return `def ${p}_body : C := ${c(l.holds)}
def ${p}_sigma : List (Nat × E) := ${sigma}
def ${p}_strong : SEntry := ${id}_proof[${i}]'(by decide +kernel)
def ${p}_strongLiteral : C := ${c(transform(leaf.laws[i]!.holds,roles,roles.scopes[i]!))}
def ${p}_weakLiteral : C := ${c(substC(l.holds,{vars:sub,maps:{},flags:{}}))}
def ${p}_weak : SEntry := {${p}_strong with law := {${p}_strong.law with holds := substC ${p}_sigma ${p}_body}}
theorem ${p}_strong_eq : ${p}_strong.law.holds = ${p}_strongLiteral := by decide +kernel
theorem ${p}_weak_eq : ${p}_weak.law.holds = ${p}_weakLiteral := by rfl
theorem ${p}_implication : SourceLawImplication ${p}_strong ${p}_weak := by
  apply sourceLawImplication_of_pointwise
  · rfl
  · rfl
  · intro ρ M h
    change evalC ρ M ${p}_weak.law.holds = true
    rw [${p}_weak_eq]
    change evalC ρ M ${p}_strong.law.holds = true at h
    rw [${p}_strong_eq] at h
    simpa [${p}_strongLiteral, ${p}_weakLiteral, evalC, and_assoc, or_assoc] using h
theorem ${sourceTheorems[j]} (ρ M) (hr : SReach ${id}_source_machine ρ M) :
    ExHolds ${p}_body ${l.forall?'(some '+ix(l.forall)+')':'none'} ${list(l.some!.map(ix))} M ${list((l.keys??[]).map(ix))} ρ := by
  have ha : SReach ${id}_ghosts.orig ρ M := ${id}_source_machine_reach ρ M hr
  have conclusion := Kern.TypedSource.ex_of_holds ${id}_ghosts ${id}_ghosts_valid ${p}_weak ${p}_sigma ${p}_body (by rfl) (by decide +kernel) (by decide +kernel) (by
    intro X N hreach
    exact ${p}_implication X N (${id}_laws X N (${id}_inclusion.sreach hreach) ${p}_strong (by exact List.getElem_mem (by decide +kernel)))) ρ M ha
  exact conclusion
`
  }).join('\n') + (source.laws.length===1 ? `\ntheorem ${id}_source (ρ M) (hr : SReach ${id}_source_machine ρ M) : ExHolds ${id}_public0_body ${source.laws[0]!.forall?'(some '+ix(source.laws[0]!.forall!)+')':'none'} ${list(source.laws[0]!.some!.map(ix))} M ${list((source.laws[0]!.keys??[]).map(ix))} ρ := ${sourceTheorems[0]} ρ M hr\n` : '')
  extra=`def ${id}_baseTyping : Typed.Typing := ${typing(roles.base)}
def ${id}_typings : List Typed.Typing := ${list(roles.scopes.map(typing))}
def ${id}_machineOption := Typed.machine ${roles.bound} ${id}_baseTyping ${raw}_machine
def ${id}_machine : SMachine := ${id}_machineOption.getD ${raw}_machine
def ${id}_options : List (Option SEntry) := (${id}_typings.zip ${raw}_proof).map fun (p,e) => Typed.entry ${roles.bound} p (Typed.withoutStepCache (Typed.withoutInitialCache e))
def ${id}_provisional : List SEntry := (${id}_options.zip ${raw}_proof).map fun (e,old) => e.getD old
-- Cache candidates are selected only by the complete root checker, never an entry number.
def ${id}_candidates (p : Typed.Typing) (e : SEntry) : List (Option SEntry) :=
  [Typed.entry ${roles.bound} p e, Typed.entry ${roles.bound} p (Typed.withoutStepCache e), Typed.entry ${roles.bound} p (Typed.withoutInitialCache e), Typed.entry ${roles.bound} p (Typed.withoutStepCache (Typed.withoutInitialCache e))]
def ${id}_choose (p : Typed.Typing) (old : SEntry) : Option SEntry :=
  ((${id}_candidates p old).filterMap id).find? fun e => checkIn (sStartGoal ${id}_machine e) e.start && checkIn (sStepGoal ${id}_machine ${id}_provisional e) e.step
def ${id}_selected : List (Option SEntry) := (${id}_typings.zip ${raw}_proof).map fun (p,e) => ${id}_choose p e
def ${id}_proof : List SEntry := (${id}_selected.zip ${raw}_proof).map fun (e,old) => e.getD old
theorem ${id}_options_complete : ${id}_machineOption.isSome && ${id}_selected.all Option.isSome = true := by decide +kernel
theorem ${id}_shape_preserved : (${id}_proof.map fun e => (Typed.treeShape e.start.2.2, Typed.treeShape e.step.2.2)) = (${raw}_proof.map fun e => (Typed.treeShape e.start.2.2, Typed.treeShape e.step.2.2)) := by decide +kernel
theorem ${id}_check : checkSMachine ${id}_machine ${id}_proof = true := by decide +kernel
theorem ${id}_laws : ∀ ρ M, SReach ${id}_machine ρ M → ∀ e ∈ ${id}_proof, e.Holds ρ M := smachine_sound _ _ ${id}_check

def ${id}_source_machine : SMachine := ${lit(source.machine)}
def ${id}_renames : List QAlpha.Rename := ${renames}
def ${id}_rowRenames : List RowAlpha.Rename := ${rows}
def ${id}_alpha := RowAlpha.renameAll (QAlpha.renameAll ${id}_source_machine ${id}_renames) ${id}_rowRenames
def ${id}_ghosts : SGhostedM := ⟨${id}_alpha, ${ghostScalars}, ${ghostStarts}, ${ghostWrites}, []⟩
theorem ${id}_alpha_valid : QAlpha.validAll ${id}_source_machine ${id}_renames = true := by decide +kernel
theorem ${id}_rows_valid : RowAlpha.validAll (QAlpha.renameAll ${id}_source_machine ${id}_renames) ${id}_rowRenames = true := by decide +kernel
theorem ${id}_ghosts_valid : smghostOk ${id}_ghosts = true := by decide +kernel
theorem ${id}_source_machine_reach (ρ M) (hr : SReach ${id}_source_machine ρ M) : SReach ${id}_ghosts.orig ρ M := by
  exact (RowAlpha.renameAll_equiv _ _ ${id}_rows_valid).symm.sreach_imp ((QAlpha.renameAll_equiv _ _ ${id}_alpha_valid).symm.sreach_imp hr)
def ${id}_source_machineAssume : C := ${c(source.machine.assume??{op:'and',xs:[]})}
def ${id}_targetAssume : C := ${c(typed.assume??{op:'and',xs:[]})}
theorem ${id}_source_machineAssume_eq : ${id}_ghosts.full.f.m.assume = ${id}_source_machineAssume := by rfl
theorem ${id}_targetAssume_eq : ${id}_machine.f.m.assume = ${id}_targetAssume := by decide +kernel
theorem ${id}_view_eq (ρ M ι κ) : sView ${id}_ghosts.full ρ M ι κ = sView ${id}_machine ρ M ι κ := by rfl
theorem ${id}_next_eq (ρ M ι κ) : sNext ${id}_ghosts.full ρ M ι κ = sNext ${id}_machine ρ M ι κ := by rfl
theorem ${id}_inclusion : SourceInclusion ${id}_ghosts.full ${id}_machine where
  inputs := by rfl
  carried := by rfl
  initial := by rfl
  startMaps := by intro M h; exact h
  pre := by intro ρ M h; exact h
  facts := by intro ρ M h; exact h
  pfacts := by intro ρ M h; exact h
  admission := by
    intro ρ M ι κ h
    rw [${id}_view_eq, ${id}_source_machineAssume_eq] at h
    rw [${id}_targetAssume_eq]
    simpa [${id}_source_machineAssume, ${id}_targetAssume, evalC, and_assoc, or_assoc] using h
  next := by intro ρ M ι κ _; exact ${id}_next_eq ρ M ι κ
${body}`
  return ''
 }})
 const stop=emitted.indexOf(`\ntheorem ${raw}_check :`)
 if(stop<0||!extra)throw Error('current complete family emitter layout changed')
 const requiredTheorems=[id+'_options_complete',id+'_shape_preserved',id+'_check',familyTheorem,id+'_alpha_valid',id+'_rows_valid',id+'_ghosts_valid',id+'_inclusion',...source.laws.map((_,j)=>id+'_public'+j+'_implication'),...sourceTheorems,...(source.laws.length===1?[id+'_source']:[]),id+'_source_machine_reach',id+'_source_machineAssume_eq',id+'_targetAssume_eq',id+'_view_eq',id+'_next_eq',...source.laws.flatMap((_,j)=>[id+'_public'+j+'_strong_eq',id+'_public'+j+'_weak_eq']),'Kern.TypedSource.ex_of_holds']
 const body='import QAlpha\nimport RowAlpha\nimport CertificateBoundSubstitution\nimport TypedSource\nopen Kern Bapa.CertificateBoundSubstitution\nset_option maxRecDepth '+options.recursionDepth+'\nset_option maxHeartbeats '+options.heartbeats+'\n'+emitted.slice(0,stop)+'\n'+extra+'\n'+requiredTheorems.map(t=>'#print axioms '+t).join('\n')+'\n'
 const project=liftProject(body,{name:'BapaProof'})
 const modules=Object.keys(project).filter(n=>n.endsWith('.lean')&&n!=='lakefile.lean').map(n=>n.slice(0,-5))
 project['lakefile.lean']='import Lake\nopen Lake DSL\npackage typed_lift\n@[default_target]\nlean_lib TypedLift where\n  roots := #['+modules.map(m=>'`'+m).join(', ')+']\n'
 if(Object.keys(project).length>options.maxFiles||Object.values(project).reduce((n,t)=>n+Buffer.byteLength(t),0)>options.maxOutputBytes)throw Error('typed output limit exceeded')
 return {project,familyTheorem,sourceTheorems,publicLawIndices,requiredTheorems,roles,status:'EMITTED_NOT_CHECKED'}
}
