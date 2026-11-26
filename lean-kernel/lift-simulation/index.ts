import type {C,E,Machine} from '../../core/machine.ts'
import {sumCovers,sumMachine,sumParts} from '../../kernel/kernel.ts'
import {leanProject,retainedSMachineToLean} from '../emit.ts'
import {leanLibrary} from '../library.ts'
import {leanTerms} from '../lean-terms.ts'
import type {PartOptions} from '../lift/proof-parts.ts'
import type {GenericLiftSource} from '../lift/source.ts'
import {sourceLeanId,sourceStructure} from '../lift/source.ts'
import {leanSource} from '../lift/project.ts'
import {planRadixSimulation,UnsupportedRadixSimulation,type RadixSimulationBundle,type RadixShapePlan} from './shape.ts'
export {planRadixSimulation,UnsupportedRadixSimulation} from './shape.ts'
export type {RadixSimulationBundle,RadixShapePlan} from './shape.ts'
export type RadixSimulationInput={id:string,bundle:RadixSimulationBundle,providedSourceAST:GenericLiftSource,options:PartOptions}
export type RadixSimulationOutput={
  project:Record<string,string>,familyTheorem:string,sourceTheorems:string[],publicLawIndices:number[],requiredTheorems:string[],
  kind:'radix-simulation',status:'EMITTED_NOT_CHECKED',parts:{familySize:number,primaryObligations:number},plan:RadixShapePlan
}
const list=(xs:(string|number)[])=>'['+xs.join(', ')+']'
const same=(a:unknown,b:unknown)=>sourceStructure(a)===sourceStructure(b)
const empty:C={op:'and',xs:[]}
const normalize=(m:Machine)=>({...m,name:'',relations:undefined,maps:m.maps??{},step:{...m.step,maps:m.step.maps??{},state:m.step.state??{},flags:m.step.flags??{}}})
function walk(x:unknown,f:(x:Record<string,unknown>)=>void):void{
  if(Array.isArray(x)){x.forEach(y=>walk(y,f));return}
  if(!x||typeof x!=='object')return
  const o=x as Record<string,unknown>;f(o);Object.values(o).forEach(y=>walk(y,f))
}
function key(p:RadixShapePlan,map:string,e:E):E{
  const layout=p.layouts.find(l=>l.map===map)
  if(!layout)return rewrite(p,e) as E
  const parts=(x:E,n:number):E[]=>{
    if(n===1)return [rewrite(p,x) as E]
    if(x.op==='tup')return [rewrite(p,x.a) as E,...parts(x.b,n-1)]
    if(x.op==='add'&&x.a.op==='mul'&&x.a.k===p.radix)return [...parts(x.a.a,n-1),rewrite(p,x.b) as E]
    if(n===3&&x.op==='add'&&x.a.op==='add'&&x.a.a.op==='mul'&&x.a.a.k===p.radix*p.radix&&x.a.b.op==='mul'&&x.a.b.k===p.radix)return [x.a.a.a,x.a.b.a,x.b].map(y=>rewrite(p,y) as E)
    if(x.op==='const'){
      let v=x.value;const ds:E[]=[];for(let i=0;i<n-1;i++){ds.unshift({op:'const',value:v%p.radix});v=Math.floor(v/p.radix)}ds.unshift({op:'const',value:v});return ds
    }
    throw new UnsupportedRadixSimulation('unsupported packed address syntax in '+map)
  }
  const tuple=(xs:E[]):E=>xs.length===1?xs[0]!:{op:'tup',a:xs[0]!,b:tuple(xs.slice(1))}
  return tuple(parts(e,layout.arity))
}
function rewrite(p:RadixShapePlan,x:unknown):unknown{
  if(Array.isArray(x))return x.map(y=>rewrite(p,y))
  if(!x||typeof x!=='object')return x
  const o=x as Record<string,unknown>
  if((o.op==='<'||o.op==='<=')&&(o.b as E)?.op==='const'&&(o.b as {value:number}).value===p.radix)return empty
  if(o.op==='get')return {...o,key:key(p,o.map as string,o.key as E)}
  return Object.fromEntries(Object.entries(o).map(([k,v])=>[k,rewrite(p,v)]))
}
function targetBase(p:RadixShapePlan):Machine{
  const m=p.sumMachine,base={...m,sums:undefined,state:Object.fromEntries(Object.entries(m.state).filter(([n])=>!Object.hasOwn(m.sums??{},n)))}
  const t=rewrite(p,base) as Machine
  t.step={...t.step,maps:Object.fromEntries(Object.entries(base.step.maps??{}).map(([name,w])=>[name,'each'in w?{...w,value:rewrite(p,w.value) as E}:{...w,key:key(p,name,w.key),value:rewrite(p,w.value) as E}]))}
  return t
}
function atoms(x:unknown):C[]{
  const out:C[]=[]
  walk(x,o=>{
    if(o.op==='flag'){out.push(o as C);return}
    if(!['=','<','<='].includes(String(o.op)))return
    const c=o as Extract<C,{a:E,b:E}>
    // Constant tests reduce directly. Boolean cell tests are discharged by
    // the checked 0-or-1 cases; splitting them again is exponential noise.
    if(c.a.op==='const'&&c.b.op==='const')return
    if(c.a.op==='get'&&c.b.op==='const'&&(c.b.value===0||c.b.value===1))return
    if(c.b.op==='get'&&c.a.op==='const'&&(c.a.value===0||c.a.value===1))return
    out.push(c)
  })
  return out.filter((c,i)=>out.findIndex(d=>same(c,d))===i)
}
function reads(x:unknown):Extract<E,{op:'get'}>[]{const out:Extract<E,{op:'get'}>[]=[];walk(x,o=>{if(o.op==='get')out.push(o as Extract<E,{op:'get'}>)});return out.filter((c,i)=>out.findIndex(d=>same(c,d))===i)}

/** The caller validates the complete capsule graph and restores its terms
 * exactly once before calling. This function never reads a capsule, restores
 * terms, invokes Lean, searches, or consumes old generated proof files. */
export function tryRadixSimulation({id,bundle,providedSourceAST:source,options}:RadixSimulationInput):RadixSimulationOutput|null{
  if(id!==sourceLeanId(source.id))throw Error('inconsistent full Lean prefix')
  for(const n of [options.maxOutputBytes,options.maxFiles,options.heartbeats,options.recursionDepth])if(!Number.isSafeInteger(n)||n<1)throw Error('finite positive generator limits required')
  const p=planRadixSimulation(bundle,source);if(!p)return null
  for(const layout of p.layouts)if(layout.arity!==2)throw new UnsupportedRadixSimulation('source invariant bridge currently supports binary tuple layouts only')
  for(const m of [source.machine,p.sumMachine])if(m.inputMaps?.length||Object.values(m.step.flags??{}).some(c=>c.op==='all'))throw new UnsupportedRadixSimulation('source/carried or pre-existing quantified flags need a separate simulation')
  for(const layout of p.layouts)if(p.sumMachine.step.maps?.[layout.map]&&'each'in p.sumMachine.step.maps[layout.map]!)throw new UnsupportedRadixSimulation('typed whole-map update needs a projection-binder bridge')
  const lowered=sumMachine(p.sumMachine).machine
  const producerMachine=Object.keys(p.producer.machine.sums??{}).length?sumMachine(p.producer.machine).machine:p.producer.machine
  if(!same(normalize(lowered),normalize(producerMachine)))throw new UnsupportedRadixSimulation('SUM declarations do not regenerate the retained producer machine exactly')
  const target=targetBase(p),sums=Object.entries(p.sumMachine.sums??{}),covers=sumCovers(p.sumMachine)
  for(const [n,d]of sums)if(d.term.op!=='get'||d.term.key.op!=='var'||d.term.key.name!==d.key)throw new UnsupportedRadixSimulation('semantic cover emitter currently requires a whole-address cell integrand: '+n)
  const free=new Set<string>([...source.machine.params,...source.machine.inputs,...Object.keys(source.machine.state),...Object.keys(source.machine.step.flags??{}).map(n=>'?'+n),...Object.keys(target.step.flags??{}).map(n=>'?'+n)])
  walk([source,p.sumMachine],o=>{if(o.op==='var')free.add(o.name as string);if(o.op==='flag')free.add('?'+String(o.name))})
  source.laws.forEach(l=>{if(l.forall)free.add(l.forall);l.keys?.forEach(k=>free.add(k))})
  for(const w of Object.values(source.machine.step.maps??{}))if('each'in w)free.add(w.each)
  for(const [n,d]of sums){const s=sumParts(n);[n,d.key,'?'+s.flag,'w?'+s.flag,s.x].forEach(v=>free.add(v))}
  const raw=id+'_retained',defs=id+'_Defs';let extra='',renderC!:(c:C)=>string,renderE!:(e:E)=>string,ix!:(n:string)=>number,mx!:(n:string)=>number
  const emitted=retainedSMachineToLean(raw,producerMachine,p.producer.laws,p.producer.proof,{free:[...free],after:(v,m,lit,c)=>{
    ix=v;mx=m;renderC=x=>`(${c(x)})`
    const vars:string[]=[],maps:string[]=[]
    for(const name of free)vars[v(name)]=name
    for(const name of Object.keys(producerMachine.maps??{}))maps[m(name)]=name
    const terms=leanTerms(vars,maps,id)
    renderE=x=>`(${terms.e(x)})`
    const ds=sums.map(([n,d])=>{const sp=sumParts(n),cells=covers[n]!.map(e=>{const map=(d.term as Extract<E,{op:'get'}>).map;return key(p,map,e)});return `⟨${v(n)}, ${v(d.key)}, ${renderE(d.term)}, ${list(cells.map(renderE))}, ${v('?'+sp.flag)}, ${v('w?'+sp.flag)}, ${v(sp.x)}, none⟩`})
    extra=`def ${id}_source : SMachine := ${lit(source.machine)}\ndef ${id}_target_data : SumMachine := ⟨${lit(target)}, ${list(ds)}⟩\n`
    extra+=source.laws.map((l,j)=>`def ${id}_source_law${j} : MLaw := ⟨${c(l.holds)}, ${l.forall?'some '+v(l.forall):'none'}⟩\ndef ${id}_source_keys${j} : List Nat := ${list((l.keys??[]).map(v))}`).join('\n')+'\n'
    const oldbase={...p.sumMachine,sums:undefined,state:Object.fromEntries(Object.entries(p.sumMachine.state).filter(([n])=>!Object.hasOwn(p.sumMachine.sums??{},n)))}
    extra+=`def ${id}_old_sums : SumMachine := ⟨${lit(oldbase)}, ${list(sums.map(([n,d])=>{const sp=sumParts(n);return `⟨${v(n)}, ${v(d.key)}, ${renderE(d.term)}, ${list(covers[n]!.map(renderE))}, ${v('?'+sp.flag)}, ${v('w?'+sp.flag)}, ${v(sp.x)}, none⟩`}))}⟩\n`
    return ''
  }})
  const cut=emitted.indexOf(`\ntheorem ${raw}_check :`);if(cut<0)throw Error('unsupported current retained emission layout')
  const retained=emitted.slice(0,cut)
  const varrefs=[...(retained+extra).matchAll(/\.var (\d+)/g)].map(m=>Number(m[1]));const freshBase=Math.max(0,...varrefs,...[...free].map(ix))+1
  const layoutLit=list(p.layouts.map(l=>`(${mx(l.map)}, ${l.arity})`))
  const sumFlags=list(sums.flatMap(([n,d])=>{const l=p.layouts.find(l=>l.map===(d.term as Extract<E,{op:'get'}>).map);return l?[`(${ix('?'+sumParts(n).flag)}, ${l.arity})`]:[]}))
  const prefix=(imports:string[])=>imports.map(i=>'import '+i).join('\n')+`\nopen Kern\nset_option maxRecDepth ${options.recursionDepth}\nset_option maxHeartbeats ${options.heartbeats}\n`
  const project=Object.assign(leanProject('',{name:'BapaProof'}),leanLibrary)
  for(const n of ['RadixKeySyntax','RadixBinderExpansion','RadixCertificateTable','RadixTupleSyntax','CertificateBoundErasure','CertificateBooleanCleanup','RadixEqualityTree','RadixCertificateTransport','FiniteSimulation','SourceInclusion'])project[n+'.lean']=leanSource(n)
  for(const n of ['RadixSumTransport','InvariantSimulation','SemanticSums'])project[n+'.lean']=leanSource(n)
  const requiredTheorems:string[]=[],printed=(n:string)=>{requiredTheorems.push(n);return '\n#print axioms '+n+'\n'}
  project[defs+'.lean']=prefix(['Lean','Sums','RadixSumTransport'])+retained+'\n'+extra+`
def ${id}_plan : Bapa.RadixSumTransport.Plan := ⟨${p.radix}, ${layoutLit}, ${freshBase}, ${sumFlags}⟩
def ${id}_outcome := Bapa.RadixSumTransport.translate ${id}_plan ${id}_old_sums ${raw}_proof
def ${id}_created : Bool := match ${id}_outcome with | .ok _ => true | .error _ => false
def ${id}_derived_proof : List SEntry := match ${id}_outcome with | .ok p => p.2 | .error _ => []
-- Materialize the closed candidate, rather than exposing the implementation of
-- its translator in the checked family's type. Reduction is only an untrusted
-- term producer: the kernel checks both the literal and proof_eq below.
open Lean Meta Elab Term in
elab "${id}_literal% " t:term : term => do
  let value ← instantiateMVars (← elabTerm t none)
  withTransparency .all <| Meta.reduce value

def ${id}_proof : List SEntry := ${id}_literal% ${id}_derived_proof
`
  // A checked family is the complete checker equality, not its semantic
  // consequence. Keep that consequence independently required as well.
  const familyTheorem=id+'_check',semanticLawsTheorem=id+'_semantic_laws'
  project[id+'_Family.lean']=prefix([defs])+`theorem ${id}_translation_succeeded : ${id}_created = true := by decide +kernel
theorem ${id}_translation_target : (Bapa.RadixSumTransport.target ${id}_plan ${id}_old_sums) = .ok ${id}_target_data := by rfl
theorem ${id}_proof_eq : ${id}_proof = ${id}_derived_proof := by with_unfolding_all rfl
theorem ${id}_family_size : ${id}_proof.length = ${p.producer.laws.length} := by decide +kernel
theorem ${id}_check : checkSMachine ${id}_target_data.plain ${id}_proof = true := by decide +kernel
theorem ${semanticLawsTheorem} : ∀ ρ M, SReach ${id}_target_data.plain ρ M → ∀ e ∈ ${id}_proof, e.Holds ρ M := smachine_sound _ _ ${id}_check
`+[id+'_translation_succeeded',id+'_translation_target',id+'_proof_eq',id+'_family_size',familyTheorem,semanticLawsTheorem].map(printed).join('')
  // Explicit law snapshots avoid normalizing complete certificate trees in
  // every semantic bridge. Equality remains a separate kernel obligation.
  let shapes='',fresh=freshBase
  const expanded=new Map<number,{first:number,rest:number[]}>()
  for(let i=0;i<p.producer.laws.length;i++){
    const l=p.producer.laws[i]!,bound=p.booleanEntries.find(b=>b.index===i),layout=bound&&p.layouts.find(q=>q.map===bound.map)
    if(layout&&l.forall){expanded.set(i,{first:ix(l.forall),rest:[fresh++]})}
  }
  for(const b of p.booleanEntries){
    const l=p.producer.laws[b.index]!,e=expanded.get(b.index),keyE=e?`(.tup (.var ${e.first}) (.var ${e.rest[0]}))`:`(.var ${ix(l.forall!)})`
    shapes+=`def ${id}_bound_entry${b.index} : SEntry := ${id}_proof[${b.index}]'(by rw [${id}_family_size]; decide +kernel)
theorem ${id}_bound_shape${b.index} : ${id}_bound_entry${b.index}.law = ⟨.le (.get ${mx(b.map)} ${keyE}) (.const 1), some ${ix(l.forall!)}⟩ ∧ ${id}_bound_entry${b.index}.keys2 = ${list(e?.rest??[])} := by constructor <;> rfl
`
    shapes+=`theorem ${id}_family_bound${b.index} (ρ M) (hl : ∀ e ∈ ${id}_proof, e.Holds ρ M) (k : Nat) : M ${mx(b.map)} k ≤ 1 := by
  have h := hl ${id}_bound_entry${b.index} (List.getElem_mem (by rw [${id}_family_size]; decide +kernel))
  change holdsOver ${id}_bound_entry${b.index}.law M ${id}_bound_entry${b.index}.keys2 ρ at h
  rw [${id}_bound_shape${b.index}.1, ${id}_bound_shape${b.index}.2] at h
  have hk := ${e?'h (cun k).2 (cun k).1':'h k'}
  simpa [evalC, evalE, upd, cpair_cun] using hk
`+printed(id+'_bound_shape'+b.index)+printed(id+'_family_bound'+b.index)
  }
  project[id+'_Shapes.lean']=prefix([id+'_Family'])+shapes
  const simplify=`${id}_target_data, ${id}_source, everyMaps, writeMaps, lookup, evalC, evalE, upd, withInputs, withCarried, decideFlags, flagSub, applyS, assoc, decideQ`
  const atomCases=(x:unknown,env:string,start=0)=>atoms(x).map((a,j)=>`  all_goals by_cases ha${start+j} : evalC ${env} M ${renderC(a)} = true`).join('\n')
  let semantic=`theorem ${id}_sum_ok : sumOk ${id}_target_data = true := by decide +kernel
theorem ${id}_sum_ghosts : sghostOk ${id}_target_data.ghosts = true := by decide +kernel
theorem ${id}_covers : Bapa.SemanticSums.Preserves ${id}_target_data ${id}_proof := by
  intro ρ M hl ι κ ha d hd k hk
  let D := (sView ${id}_target_data.plain ρ M ι κ).1
  clear ha
  simp only [${id}_target_data, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
  rcases hd with ${sums.map(()=> 'rfl').join(' | ')}
`
  sums.forEach(([name,d])=>{
    const mp=(d.term as Extract<E,{op:'get'}>).map,w=target.step.maps?.[mp],env=w&&'each'in w?`(upd D ${ix(w.each)} k)`:'D'
    semantic+=`  · change everyMaps ${id}_target_data.s D M ${mx(mp)} k = M ${mx(mp)} k
    change k ∉ ${list(covers[name]!.map(e=>`evalE D M ${renderE(key(p,mp,e))}`))} at hk
`
    const b=p.booleanEntries.find(b=>b.map===mp)
    if(b)semantic+=`    have hb := ${id}_family_bound${b.index} ρ M hl k
    have hz : M ${mx(mp)} k = 0 ∨ M ${mx(mp)} k = 1 := by omega
    rcases hz with hz | hz
`
    semantic+=atomCases(w,env).replace(/^  /gm,'    ')+'\n'+`    all_goals simp_all [${simplify}]
`
  })
  semantic+=`theorem ${id}_exact_sums : ∀ ρ M, SReach ${id}_target_data.plain ρ M → ∀ d ∈ ${id}_target_data.sums, IsSum (gAt d.g M) (ρ d.v) :=
  Bapa.SemanticSums.sum_holds _ ${id}_check ${id}_sum_ok (by decide +kernel) ${id}_covers
theorem ${id}_own_admission : ∀ ρ M, SReach ${id}_target_data.plain ρ M → ∀ ι κ,
    evalC (sView ${id}_target_data.plain ρ M ι κ).1 (sView ${id}_target_data.plain ρ M ι κ).2 ${id}_target_data.plain.f.m.assume =
    evalC (sView ${id}_target_data.plain ρ M ι κ).1 (sView ${id}_target_data.plain ρ M ι κ).2 ${id}_target_data.s.f.m.assume :=
  Bapa.SemanticSums.sum_allowed _ ${id}_check ${id}_sum_ok (by decide +kernel) ${id}_covers
theorem ${id}_integrands : ${id}_target_data.sums.map (·.g) = ${id}_old_sums.sums.map (·.g) := by rfl
`
  // Project only the ghost-independent kind entries; the inferred SUM law
  // itself intentionally mentions sum variables and cannot be projected.
  for(const b of p.booleanEntries){
    const e=expanded.get(b.index)
    semantic+=`theorem ${id}_base_bound${b.index} (ρ M) (hr : SReach ${id}_target_data.s ρ M) (k : Nat) : M ${mx(b.map)} k ≤ 1 := by
  have h := Bapa.SemanticSums.sum_project_laws _ ${id}_sum_ghosts ${id}_proof ${id}_check ${id}_sum_ok (by decide +kernel) ${id}_covers ρ M hr ${id}_bound_entry${b.index} (List.getElem_mem (by rw [${id}_family_size]; decide +kernel)) (by decide +kernel)
  change holdsOver ${id}_bound_entry${b.index}.law M ${id}_bound_entry${b.index}.keys2 ρ at h
  rw [${id}_bound_shape${b.index}.1, ${id}_bound_shape${b.index}.2] at h
  have hk := ${e?'h (cun k).2 (cun k).1':'h k'}
  simpa [evalC, evalE, upd, cpair_cun] using hk
`
  }
  semantic+=[id+'_sum_ok',id+'_sum_ghosts',id+'_covers',id+'_exact_sums',id+'_own_admission',id+'_integrands',...p.booleanEntries.map(b=>id+'_base_bound'+b.index)].map(printed).join('')
  project[id+'_Sums.lean']=prefix([id+'_Shapes','SemanticSums'])+semantic
  // Source templates are syntax-specialized equality proofs, with all cell
  // normalizations guarded by bounds obtained from the target checked family.
  const inv=p.booleanEntries.map(b=>`(∀ k, x.2 ${mx(b.map)} k ≤ 1)`).join(' ∧ '),invAt=(b:number)=>'h'+'.2'.repeat(b)+(b===p.booleanEntries.length-1?'':'.1')
  let bridge=`def ${id}_Inv (x : Bapa.FiniteSimulation.KState) : Prop := ${inv}
theorem ${id}_invariant (ρ M) (hr : SReach ${id}_target_data.s ρ M) : ${id}_Inv (ρ,M) := by
  ${p.booleanEntries.length>1?'refine ⟨'+p.booleanEntries.map(()=>'?_').join(', ')+'⟩':''}
${p.booleanEntries.map(b=>`  ${p.booleanEntries.length>1?'· ':''}exact ${id}_base_bound${b.index} ρ M hr`).join('\n')}
`
  const fromInv=(x:unknown,env:string)=>{
    const rs=reads(x).flatMap(r=>{const bi=p.booleanEntries.findIndex(b=>b.map===r.map);return bi<0?[]:[{r,bi}]})
    return rs.map(({r,bi},j)=>`  have hb${j} := ${invAt(bi)} (evalE ${env} M ${renderE(r.key)})\n  have hz${j} : M ${mx(r.map)} (evalE ${env} M ${renderE(r.key)}) = 0 ∨ M ${mx(r.map)} (evalE ${env} M ${renderE(r.key)}) = 1 := by omega`).join('\n')+'\n'+rs.map((_,j)=>`  all_goals rcases hz${j} with hz${j} | hz${j}`).join('\n')
  }
  const mapNames=Object.keys(target.maps??{})
  const mapCases=(i:number,indent:string):string=>{
    const name=mapNames[i]
    if(name===undefined)return indent+`simp_all [${simplify}]`
    const w=source.machine.step.maps?.[name],env=w&&'each'in w?`(upd D ${ix(w.each)} k)`:'D'
    const branch=[fromInv(w,env),atomCases(w,env),`  all_goals simp_all [${simplify}]`].join('\n').replace(/^  /gm,indent+'  ')
    return indent+`by_cases hm${i} : ${mx(name)} = mp\n`+indent+`· subst mp\n`+branch+'\n'+indent+'·\n'+mapCases(i+1,indent+'  ')
  }
  const viewFlags=[...new Set([...Object.keys(source.machine.step.flags??{}),...Object.keys(target.step.flags??{})])].map(n=>ix('?'+n))
  const viewCases=(i:number,indent:string):string=>i===viewFlags.length?indent+`simp_all [sView, ${simplify}]`:
    indent+`by_cases hv${i} : ${viewFlags[i]} = v\n`+indent+`· subst v\n`+indent+`  simp_all [sView, ${simplify}]\n`+indent+`·\n`+viewCases(i+1,indent+'  ')
  const inputEnv=`(withInputs ${id}_source.f.m.inputs ρ ι)`
  bridge+=`theorem ${id}_view (ρ M ι κ) (h : ${id}_Inv (ρ,M)) : sView ${id}_source ρ M ι κ = sView ${id}_target_data.s ρ M ι κ := by
  change ${inv.replaceAll('x.2','M')} at h
${fromInv(source.machine.step.flags,inputEnv)}
  all_goals apply Prod.ext
  all_goals first | rfl | (
    funext v
${viewCases(0,'    ')}
  )
theorem ${id}_maps (D M) (h : ${id}_Inv (D,M)) : everyMaps ${id}_source D M = everyMaps ${id}_target_data.s D M := by
  change ${inv.replaceAll('x.2','M')} at h
  funext mp k
${mapCases(0,'  ')}
theorem ${id}_next (ρ M ι κ) (h : ${id}_Inv (ρ,M)) : sNext ${id}_source ρ M ι κ = sNext ${id}_target_data.s ρ M ι κ := by
  unfold sNext
  rw [${id}_view ρ M ι κ h]
  apply Prod.ext
  · rfl
  · apply ${id}_maps
    exact h
`
  bridge+=`theorem ${id}_restricted : Bapa.InvariantSimulation.RestrictedInclusion ${id}_source ${id}_target_data.s ${id}_Inv where
  initial := by
    rintro x ⟨ρ,M,hm,hp,hf,hpf,rfl⟩
    refine ⟨ρ,M,?_,?_,?_,?_,?_⟩
    · simpa [StartMaps, ${id}_source, ${id}_target_data, and_comm] using hm
    · simpa [${id}_source, ${id}_target_data, evalC, evalE] using hp
    · simpa [${id}_source, ${id}_target_data] using hf
    · simpa [SMachine.PFacts, ${id}_source, ${id}_target_data] using hpf
    · rfl
  admission := by
    intro ρ M ι κ h ha
    rw [${id}_view ρ M ι κ h] at ha
    simp_all [${id}_source, ${id}_target_data, evalC, evalE]
  next := by intro ρ M ι κ h _; exact ${id}_next ρ M ι κ h
theorem ${id}_simulation : Bapa.FiniteSimulation.SSimulation ${id}_source ${id}_target_data.s (Bapa.InvariantSimulation.Relation ${id}_Inv) := ${id}_restricted.simulation ${id}_invariant
`
  const sourceTheorems=source.laws.map((_,j)=>id+'_source_law'+j+'_holds')
  source.laws.forEach((l,j)=>{
    const n=p.publicLawIndices[j]!,strong=id+'_public_entry'+j
    bridge+=`def ${strong} : SEntry := ${id}_proof[${n}]'(by rw [${id}_family_size]; decide +kernel)
theorem ${sourceTheorems[j]} (ρ M) (hr : SReach ${id}_source ρ M) : holdsOver ${id}_source_law${j} M ${id}_source_keys${j} ρ := by
  have ht := ${id}_restricted.sreach ${id}_invariant hr
  have h := Bapa.SemanticSums.sum_project_laws _ ${id}_sum_ghosts ${id}_proof ${id}_check ${id}_sum_ok (by decide +kernel) ${id}_covers ρ M ht ${strong} (List.getElem_mem (by rw [${id}_family_size]; decide +kernel)) (by decide +kernel)
  change holdsOver ${strong}.law M ${strong}.keys2 ρ at h
  have shape : ${strong}.law = ⟨${renderC(rewrite(p,p.producer.laws[n]!.holds) as C)}, ${l.forall?'some '+ix(l.forall):'none'}⟩ ∧ ${strong}.keys2 = ${list((l.keys??[]).map(ix))} := by constructor <;> rfl
  rw [shape.1, shape.2] at h
  simp only [holdsOver, MLaw.Holds, ${id}_source_law${j}, ${id}_source_keys${j}] at h ⊢
${[...(l.keys??[]),...(l.forall?[l.forall]:[])].map((_,i)=>`  intro k${i}`).join('\n')}
  have hp := h ${[...(l.keys??[]),...(l.forall?[l.forall]:[])].map((_,i)=>'k'+i).join(' ')}
  simp [evalC, evalE, upd] at hp ⊢
  omega
`
  })
  bridge+=[id+'_invariant',id+'_view',id+'_maps',id+'_next',id+'_restricted',id+'_simulation',...sourceTheorems].map(printed).join('')
  project['BapaProof.lean']=prefix([id+'_Sums','InvariantSimulation'])+bridge
  const modules=Object.keys(project).filter(n=>n.endsWith('.lean')&&n!=='lakefile.lean').map(n=>n.slice(0,-5))
  project['lakefile.lean']='import Lake\nopen Lake DSL\npackage radixsimulation\n@[default_target]\nlean_lib RadixSimulation where\n  roots := #['+modules.map(n=>'`'+n).join(', ')+']\n'
  if(Object.keys(project).length>options.maxFiles||Object.values(project).reduce((n,s)=>n+Buffer.byteLength(s),0)>options.maxOutputBytes)throw Error('complete radix simulation project exceeds output budget')
  return {project,familyTheorem,sourceTheorems,publicLawIndices:p.publicLawIndices,requiredTheorems,kind:'radix-simulation',status:'EMITTED_NOT_CHECKED',parts:{familySize:p.producer.laws.length,primaryObligations:2*p.producer.laws.length},plan:p}
}
