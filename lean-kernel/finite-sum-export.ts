import type {Law,Machine} from '../core/machine.ts'
import {checkFiniteSum,finiteSumTheory,sumLocalGoal,type FiniteSumCertificate} from '../kernel/finite-sum.ts'
import {encode,machineLit} from './emit.ts'
import {leanTerms} from './lean-terms.ts'

// Replay the retained local trees verbatim. Only the syntax-to-semantics
// adapter is generated; induction/finite addition use the general theorem.
export function finiteSumToLean(id:string,m:Machine,law:Law,certificate:FiniteSumCertificate):string {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(id) || !checkFiniteSum(m,law,certificate)) throw Error('invalid finite-sum export')
  const {layout:p,trees}=certificate, {locals,point,coordinate,reset:resetTerm}=finiteSumTheory(m,law,p)!
  const write=m.step.maps![p.map]!
  if (!('each' in write)) throw Error('expected broadcast write')
  const names=[...new Set([...m.params,...m.inputs,...Object.keys(m.state),...Object.keys(m.step.flags??{}).map(f=>`?${f}`),write.each,coordinate])]
  const maps=[p.map], t=leanTerms(names,maps,'finite-sum')
  const index=(name:string)=>{ const i=names.indexOf(name); if (i<0) throw Error(`unknown finite-sum name ${name}`); return i }
  const mx=(map:string)=>{ if (map!==p.map) throw Error(`unknown finite-sum map ${map}`); return 0 }
  const certs=locals.map(loc=>{
    const goal=sumLocalGoal(loc), cert=encode({name:loc.name,goal,tree:trees[loc.name]!},false,true,names,maps)
    const hypotheses=loc.assumptions.map((h,i)=>` (h${i} : holdsC env maps (${t.c(h)}))`).join('')
    const cases=goal.hyps.map(()=> 'rfl').join(' | ')
    return `def ${loc.name}_goal : Kern.Goal := ⟨${cert.tab}, ${cert.hyps}⟩
def ${loc.name}_tree : Kern.Tree := ${cert.tree}
theorem ${loc.name}_check : checkGoal ${loc.name}_goal ${loc.name}_tree = true := by decide +kernel
theorem checked_${loc.name} (env : Nat → Nat) (maps : Nat → Nat → Nat)${hypotheses} :
    holdsC env maps (${t.c(loc.conclusion)}) := by
  apply Classical.byContradiction
  intro h
  apply sound ${loc.name}_goal ${loc.name}_tree ${loc.name}_check env maps
  intro c hc
  simp only [${loc.name}_goal, List.mem_cons, List.mem_nil_iff, or_false] at hc
${goal.hyps.length===1?'  subst c':`  rcases hc with ${cases}`}
${loc.assumptions.map((_,i)=>`  · exact (evalC_iff env maps _).2 h${i}\n`).join('')}  ${loc.assumptions.length?'· ':''}exact (evalC_iff env maps _).2 h`
  }).join('\n\n')
  const addr=(v:string)=>p.offset?`(${v} + ${p.offset})`:v
  const bound=index(p.bound), defCell=m.maps![p.map]!, fields=p.fields.map(f=>({...f,i:index(f.field)}))
  const indices=fields.map(f=>f.i).join(',')
  const tags=fields.map(f=>`if i = ${f.i} then ${f.value} else `).join('')+'0'
  const arr=(n:number)=>Array.from({length:n},()=> 'rfl').join(' | ')
  const sem='src, before, applyS, assoc, lookup, evalE, evalC, holdsC, upd, everyMaps, decideFlags, flagSub, withInputs, -List.elem_eq_contains'
  const prev='(before ρ ι)', next='(sNext src ρ M ι κ)', shift=`(upd X ${index(coordinate)} j)`
  const stepvars='(ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)'
  const grouping=fields.map(f=>`countCell ${f.value} M j`).reduce((a,b)=>`(${a} + ${b})`)
  const cap=fields.map(f=>`ρ ${f.i}`).reduce((a,b)=>`(${a} + ${b})`)
  const start=fields.map((f,i)=>`  · have h0 : (applyS src.f.m.init ρ M) ${f.i} = 0 := by
      simpa [${sem}] using checked_field${i}_init ρ M
    exact ⟨h0.trans (sumBelow_zero_fn _).symm, fun j _ => by
      change countCell ${f.value} M j = 0
      simp [countCell, initMap]⟩`).join('\n')
  const reset=fields.map((f,i)=>`    · have hz : ρ' ${f.i} = 0 := by
        simp only [ρ', sNext, view_eq, Prod.fst, Prod.snd]
        simpa [X, ${sem}] using checked_field${i}_reset X M ha hr
      exact ⟨hz.trans (sumBelow_zero_fn _).symm, fun j _ => by
        change countCell ${f.value} M' j = 0
        simp [countCell, resetMap]⟩`).join('\n')
  const delta=fields.map((f,i)=>`        · have hdelta : ρ' ${f.i} + countCell ${f.value} M q = ρ ${f.i} + countCell ${f.value} M' q := by
            simp only [ρ', M', countCell, sNext, view_eq, Prod.fst, Prod.snd]
            simpa [q, point, X, ${sem}] using checked_field${i}_delta X M ha hr
          simpa [layout, sumOn] using hdelta`).join('\n')
  const resetC=t.c(resetTerm)
  return `namespace ${id}
open Kern Classical Kern.FiniteSumComposition
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def src : SMachine := ${machineLit(m,t,index,mx)}
def original : C := ${t.c(law.holds)}
def before (ρ ι : Nat → Nat) := withInputs src.f.m.inputs ρ ι
def point (X : Nat → Nat) (M : Nat → Nat → Nat) := evalE X M (${t.e(point)})
def countCell (tag : Nat) (M : Nat → Nat → Nat) (j : Nat) : Nat := if M 0 ${addr('j')} = tag then 1 else 0
def layout : Layout := ⟨[${indices}], fun s => s.1 ${bound}, fun i s => countCell (${tags}) s.2⟩

theorem view_eq ${stepvars} : sView src ρ M ι κ = (decideFlags src.f.flags ${prev} M, M) := by
  have hm : withCarried src M κ = M := by funext i j; rfl
  have hv : decideQ src ${prev} M = ${prev} := by funext i; simp [decideQ, src, lookup]
  simp only [sView, hm]
  change (decideFlags src.f.flags (decideQ src ${prev} M) M, M) = _
  rw [hv]

theorem assume_eq ${stepvars}
    (h : evalC (sView src ρ M ι κ).1 (sView src ρ M ι κ).2 src.f.m.assume = true) :
    holdsC ${prev} M (${t.c(locals[0]!.assumptions[0]!)}) := by
  rw [view_eq] at h
  simpa [${sem}] using h

theorem bound_next ${stepvars} : ${next}.1 ${bound} = ρ ${bound} := by
  simp only [sNext, view_eq, Prod.fst, Prod.snd]
  simp [${sem}]
${certs}

theorem layout_base (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hm : StartMaps src.f.m M) :
    Coupled layout (applyS src.f.m.init ρ M, M) := by
  have initMap (j : Nat) : M 0 j = ${defCell} := hm (0,${defCell}) (by simp [src]) j
  apply rebuilt_coupled layout
  refine ⟨fun _ _ => 0, ?_⟩
  intro i hi
  simp only [layout, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ${arr(fields.length)}
${start}

theorem layout_next ${stepvars}
    (adm : evalC (sView src ρ M ι κ).1 (sView src ρ M ι κ).2 src.f.m.assume = true) :
    StepOK layout (ρ, M) ${next} := by
  let X := before ρ ι
  let N := ρ ${bound}
  let q := point X M
  let ρ' := ${next}.1
  let M' := ${next}.2
  have hn : ρ' ${bound} = N := bound_next ρ M ι κ
  have hb : X ${bound} = N := by rfl
  have ha := assume_eq ρ M ι κ adm
  have hq : q < N := by simpa only [q, point, holdsC, evalE, hb] using checked_point_inside X M ha
  have haAt (j : Nat) : holdsC ${shift} M (${t.c(locals[0]!.assumptions[0]!)}) := by
    simpa [holdsC, evalE, upd] using ha
  have hqAt (j : Nat) : point ${shift} M = q := by simp [point, evalE, upd, q]
  refine ⟨hn, ?_⟩
  by_cases hr : holdsC X M (${resetC})
  · have hrAt (j : Nat) : holdsC ${shift} M (${resetC}) := by simpa [holdsC, evalE, upd] using hr
    have resetMap (j : Nat) : M' 0 ${addr('j')} = ${defCell} := by
      have v := checked_broadcast_reset ${shift} M (haAt j) (hrAt j)
      simp only [M', sNext, view_eq, Prod.fst, Prod.snd]
      simpa [X, ${sem}] using v
    refine Or.inr ⟨fun _ _ => 0, ?_⟩
    intro i hi
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with ${arr(fields.length)}
${reset}
  · have hrAt (j : Nat) : ¬holdsC ${shift} M (${resetC}) := by simpa [holdsC, evalE, upd] using hr
    have frameMap (j : Nat) (hne : j ≠ q) : M' 0 ${addr('j')} = M 0 ${addr('j')} := by
      have hneq : holdsC ${shift} M (${t.c(locals[1]!.assumptions[2]!)}) := by
        change j ≠ point ${shift} M
        rwa [hqAt]
      have v := checked_other_cells_frame ${shift} M (haAt j) (hrAt j) hneq
      simp only [M', sNext, view_eq, Prod.fst, Prod.snd]
      simpa [X, ${sem}] using v
    refine Or.inl ⟨[q], by simp, ?_, ?_⟩
    · simpa [layout, N] using hq
    · intro i hi
      constructor
      · intro j _ hne
        change countCell _ M' j = countCell _ M j
        simp [countCell, frameMap j (by simpa using hne)]
      · simp only [layout, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with ${arr(fields.length)}
${delta}

theorem original_law {ρ M} (h : SReach src ρ M) : holdsC ρ M original := by
  apply state_law src layout original (fun _ _ => 1) layout_base layout_next _ _ h
  · rintro ⟨ρ, M⟩ j _
    have v := checked_disjoint_capacity (upd ρ ${index(coordinate)} j) M
    have hc : ${grouping} ≤ 1 := by simpa [countCell, holdsC, evalE, evalC, upd] using v
    simpa [layout, sumOn, Nat.add_assoc] using hc
  · rintro ⟨ρ, M⟩ hcap
    apply checked_capacity_entails_claim
    change ${cap} ≤ ρ ${bound}
    simpa [layout, sumOn, sumBelow_const, Nat.add_assoc] using hcap

end ${id}
#print axioms ${id}.original_law
`
}
