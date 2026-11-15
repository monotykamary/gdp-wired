// Alpha-only source projection. The rename proposals are untrusted; QAlpha checks
// capture avoidance and equality of the entire rendered machine in Lean.
import type {Machine, Law} from '../../core/machine.ts'
import {boundOf} from '../../kernel/kernel.ts'
import {retainedSMachineToLean} from '../../lean-kernel/emit.ts'
import {inspectProvenance, lawCoverage, type NativeBundle} from './proof-capture.ts'

type Rename = {flag:string, old:string, fresh:string}
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

// Caller must restore the capsule's term prelude first. This only accepts a
// plain, unique retained family; inferred, counted and witness routes need their
// own semantic bridge. Every public claim is rendered from the original law.
export function emitAlphaSource(id:string, bundle:NativeBundle):string {
  if (bundle.schema !== 'bapa-proof/v1' || bundle.route !== 'plain' || !bundle.verdict.proven || !bundle.verdict.checked)
    throw Error('alpha source projection requires a checked plain family')
  const found=inspectProvenance(bundle.proof)
  if(found.route !== 'plain' || found.counted.length || found.usual.length !== 1)
    throw Error('alpha source projection requires one plain usual family')
  const leaf=found.usual[0]!, source=bundle.original.machine, laws=bundle.original.laws
  if(source.history || source.sums && Object.keys(source.sums).length || Object.keys(source.fns ?? {}).length)
    throw Error('source machine requires a separately qualified semantic route')
  if(!laws.length || laws.some(l=>l.stated!==undefined||l.some!==undefined||l.ex!==undefined||l.finite!==undefined||l.witness!==undefined))
    throw Error('alpha source projection supports only nonempty ordinary public laws')
  if(Object.keys(source.counts??{}).length||Object.keys(leaf.machine.counts??{}).length)
    throw Error('counted source requires its own semantic bridge')
  const indices=lawCoverage(laws,leaf.laws), rs=alphaProposals(source,leaf.machine)
  const free=[...new Set(Object.values(source.step.flags ?? {}).flatMap(q=>q.op==='all'?boundOf(q):[]))]
  return retainedSMachineToLean(id,leaf.machine,leaf.laws,leaf.proof,{free,after:(ix,_mx,lit,c)=>{
    const renames=rs.map(r=>`⟨${ix(`?${r.flag}`)}, ${ix(r.old)}, ${ix(r.fresh)}⟩`).join(', ')
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
theorem ${id}_alpha_valid : Kern.QAlpha.validAll ${id}_source ${id}_source_renames = true := by decide +kernel
theorem ${id}_alpha_result : Kern.QAlpha.renameAll ${id}_source ${id}_source_renames = ${id}_machine := by rfl
theorem ${id}_source_laws : ∀ ρ M, SReach ${id}_source ρ M → ∀ e ∈ ${id}_proof, e.Holds ρ M := by
  intro ρ M hr e he
  have eqv := Kern.QAlpha.renameAll_equiv ${id}_source ${id}_source_renames ${id}_alpha_valid
  have hp : SReach ${id}_machine ρ M := by
    rw [← ${id}_alpha_result]
    exact eqv.symm.sreach_imp hr
  exact ${id}_laws ρ M hp e he
${claims}`
  }})
}
