// Alpha-only source projection. The rename proposals are untrusted; QAlpha checks
// capture avoidance and equality of the entire rendered machine in Lean.
import type {Machine, Law} from '../../core/machine.ts'
import {boundOf} from '../../kernel/kernel.ts'
import {retainedSMachineToLean} from '../../lean-kernel/emit.ts'
import {inspectProvenance, lawCoverage, qualifyProjection, type NativeBundle} from './proof-capture.ts'

type Rename = {flag:string, old:string, fresh:string}
type RowRename = {map:string, old:string, fresh:string}
export function alphaProposals(source:Machine, producer:Machine): Rename[] {
  const result:Rename[] = []
  for (const [flag, q] of Object.entries(source.step.flags ?? {})) {
    const p = producer.step.flags?.[flag]
    if (q.op !== 'all' || p?.op !== 'all') continue
    const a=boundOf(q), b=boundOf(p)
    if (a.length !== b.length) throw Error(`quantified flag arity differs: ${flag}`)
    for (let i=0;i<a.length;i++) if(a[i]!==b[i]) result.push({flag,old:a[i]!,fresh:b[i]!})
  }
  return result
}

// Row updates have a separate local binder. Like quantified renames these are
// proposals only; RowAlpha checks capture avoidance and operational equivalence.
export function rowAlphaProposals(source:Machine,producer:Machine):RowRename[]{
 const result:RowRename[]=[]
 for(const [map,w]of Object.entries(source.step.maps??{})){
  const p=producer.step.maps?.[map]
  if('each'in w&&p&&'each'in p&&w.each!==p.each)result.push({map,old:w.each,fresh:p.each})
 }
 return result
}

// Caller must restore the capsule's term prelude first. This only accepts a
// plain family or an inferred family with an identical machine or proposed
// quantified-binder renames. The entire machine equality is still checked in
// Lean; a proposal is never source acceptance. Counted and witness routes remain separate.
export function emitAlphaSource(id:string, bundle:NativeBundle):string {
  if (bundle.schema !== 'bapa-proof/v1' || !['plain','inferred'].includes(bundle.route) || !bundle.verdict.proven || !bundle.verdict.checked)
    throw Error('alpha source projection requires a checked usual family')
  const found=inspectProvenance(bundle.proof)
  if(found.route !== bundle.route || found.counted.length || found.usual.length !== 1)
    throw Error('alpha source projection requires one complete usual family')
  const leaf=found.usual[0]!, source=bundle.original.machine, laws=bundle.original.laws
  if(source.history || source.sums && Object.keys(source.sums).length || Object.keys(source.fns ?? {}).length)
    throw Error('source machine requires a separately qualified semantic route')
  if(!laws.length || laws.some(l=>l.stated!==undefined||l.some!==undefined||l.ex!==undefined||l.finite!==undefined||l.witness!==undefined))
    throw Error('alpha source projection supports only nonempty ordinary public laws')
  if(Object.keys(source.counts??{}).length||Object.keys(leaf.machine.counts??{}).length)
    throw Error('counted source requires its own semantic bridge')
  const indices=lawCoverage(laws,leaf.laws), rs=alphaProposals(source,leaf.machine), rows=rowAlphaProposals(source,leaf.machine)
  if(bundle.route==='inferred'&&!rs.length&&!rows.length&&qualifyProjection(bundle.original,leaf.machine,leaf.laws).kind!=='same-machine')
    throw Error('inferred source projection requires the same source machine or proposed quantified-binder renames')
  const free=[...new Set([...Object.values(source.step.flags ?? {}).flatMap(q=>q.op==='all'?boundOf(q):[]),...Object.values(source.step.maps??{}).flatMap(w=>'each'in w?[w.each]:[])])]
  return retainedSMachineToLean(id,leaf.machine,leaf.laws,leaf.proof,{free,after:(ix,mx,lit,c)=>{
    const renames=rs.map(r=>`⟨${ix(`?${r.flag}`)}, ${ix(r.old)}, ${ix(r.fresh)}⟩`).join(', ')
    const rowRenames=rows.map(r=>`⟨${mx(r.map)}, ${ix(r.old)}, ${ix(r.fresh)}⟩`).join(', ')
    const claims=laws.map((law:Law,j:number)=>{
      const k=indices[j]!, keys=`[${(law.keys ?? []).map(ix).join(', ')}]`
      return `def ${id}_source_law${j} : MLaw := ⟨${c(law.holds)}, ${law.forall ? `some ${ix(law.forall)}` : 'none'}⟩
theorem ${id}_source_law${j}_eq : ${id}_source_law${j} = ${id}_e${k}.law := by rfl
theorem ${id}_source_keys${j}_eq : ${keys} = ${id}_e${k}.keys2 := by rfl
theorem ${id}_source_law${j}_holds (ρ M) (hr : SReach ${id}_source ρ M) : holdsOver ${id}_source_law${j} M ${keys} ρ := by
  have hm : ${id}_e${k} ∈ ${id}_proof := by simp [${id}_proof]
  have h := ${id}_source_laws ρ M hr ${id}_e${k} hm
  simpa only [SEntry.Holds, ${id}_source_law${j}_eq, ${id}_source_keys${j}_eq] using h`
    }).join('\n')
    return `def ${id}_source : SMachine := ${lit(source)}
def ${id}_source_renames : List Kern.QAlpha.Rename := [${renames}]
def ${id}_source_row_renames : List Kern.RowAlpha.Rename := [${rowRenames}]
theorem ${id}_alpha_valid : Kern.QAlpha.validAll ${id}_source ${id}_source_renames = true := by decide +kernel
theorem ${id}_row_valid : Kern.RowAlpha.validAll (Kern.QAlpha.renameAll ${id}_source ${id}_source_renames) ${id}_source_row_renames = true := by decide +kernel
theorem ${id}_alpha_result : Kern.RowAlpha.renameAll (Kern.QAlpha.renameAll ${id}_source ${id}_source_renames) ${id}_source_row_renames = ${id}_machine := by rfl
theorem ${id}_source_laws : ∀ ρ M, SReach ${id}_source ρ M → ∀ e ∈ ${id}_proof, e.Holds ρ M := by
  intro ρ M hr e he
  have eqv := Kern.QAlpha.renameAll_equiv ${id}_source ${id}_source_renames ${id}_alpha_valid
  have hp : SReach ${id}_machine ρ M := by
    rw [← ${id}_alpha_result]
    have row := Kern.RowAlpha.renameAll_equiv (Kern.QAlpha.renameAll ${id}_source ${id}_source_renames) ${id}_source_row_renames ${id}_row_valid
    exact row.symm.sreach_imp (eqv.symm.sreach_imp hr)
  exact ${id}_laws ρ M hp e he
${claims}
#print axioms ${id}_row_valid`
  }})
}
