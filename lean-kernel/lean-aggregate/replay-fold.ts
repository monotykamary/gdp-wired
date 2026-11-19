import assert from 'node:assert/strict'
import {encode,machineLit} from '../../lean-kernel/emit.ts'
import {leanTerms} from '../../lean-kernel/lean-terms.ts'
import {checkPointFold,foldTheory,localGoal,type FoldPacket} from './point-fold.ts'

export function emitPointFold(packet: FoldPacket): string {
  assert(checkPointFold(packet))
  const {machine:m,laws:[law]}=packet, theory=foldTheory(m,law!)!
  const {proposal:p,coordinate,locals,point}=theory
  const writes = m.step.maps![p.map]!
  assert('each' in writes)
  assert(theory.bound.op==='var')
  const names = [...new Set([...m.params,...m.inputs,...Object.keys(m.state),...Object.keys(m.step.flags ?? {}).map(f=>`?${f}`),writes.each,coordinate])]
  const maps=[p.map], t=leanTerms(names,maps,'finite fold'), ix=(x:string)=>{const i=names.indexOf(x);assert(i>=0,x);return i}, mx=(name:string)=>{assert.equal(name,p.map);return 0}
  const certs=locals.map(loc=>{
    const goal=localGoal(loc), cert=encode({name:loc.name,goal,tree:packet.trees[loc.name]!},false,true,names,maps)
    const hypotheses=loc.assumptions.map((h,i)=>` (h${i} : holdsC env maps (${t.c(h)}))`).join('')
    const choices=Array.from({length:goal.hyps.length},()=> 'rfl').join(' | ')
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
${goal.hyps.length===1?'  subst c':`  rcases hc with ${choices}`}
${loc.assumptions.map((_,i)=>`  · exact (evalC_iff env maps _).2 h${i}`).join('\n')}
  ${loc.assumptions.length?'· ':''}exact (evalC_iff env maps _).2 h`
  }).join('\n\n')
  const boundIx=ix(theory.bound.name), addr=(v:string)=>p.offset? `(${v} + ${p.offset})` : v
  const sem='src, before, applyS, assoc, lookup, evalE, evalC, holdsC, upd, everyMaps, decideFlags, flagSub, withInputs, -List.elem_eq_contains'
  const shift=(v:string)=>`(upd X ${ix(coordinate)} ${v})`
  const stepvars='(ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)'
  const prev='(before ρ ι)', next='(sNext src ρ M ι κ)'
  const cap=p.fields.map(f=>`ρ ${ix(f.field)}`).reduce((a,b)=>`(${a} + ${b})`)
  const classBody=(mp:string)=>p.fields.map(f=>`countCell ${f.value} ${mp} j`).reduce((a,b)=>`(${a} + ${b})`)
  const bindStep=(f:(typeof p.fields)[number],i:number) => `
  · have h0 : (applyS src.f.m.init ρ M) ${ix(f.field)} = 0 := by
      simpa [${sem}] using checked_field${i}_init ρ M
    change (applyS src.f.m.init ρ M) ${ix(f.field)} = sumBelow (countCell ${f.value} M) (applyS src.f.m.init ρ M ${boundIx})
    rw [h0]
    apply Eq.symm
    exact zeroSum _ _ (by intro j; simp [countCell, hMap])`
  return `import FiniteFold
import Ghost
open Kern FiniteFold
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def src : SMachine := ${machineLit(m,t,ix,mx)}
def original : C := ${t.c(law!.holds)}
def before (ρ ι : Nat → Nat) : Nat → Nat := withInputs src.f.m.inputs ρ ι
def point (X : Nat → Nat) (M : Nat → Nat → Nat) := evalE X M (${t.e(point)})
def countCell (tag : Nat) (M : Nat → Nat → Nat) (j : Nat) : Nat := if M 0 ${addr('j')} = tag then 1 else 0

def Coupled (ρ : Nat → Nat) (M : Nat → Nat → Nat) : Prop :=
  ${p.fields.map(f=>`(ρ ${ix(f.field)} = sumBelow (countCell ${f.value} M) (ρ ${boundIx}))`).join(' ∧ ')}

theorem zeroSum (f : Nat → Nat) (N : Nat) (h : ∀ j, f j = 0) : sumBelow f N = 0 := by
  rw [← sumBelow_zero_fn N]
  exact sumBelow_congr N (fun j _ => h j)

theorem view_eq ${stepvars} :
    sView src ρ M ι κ = (decideFlags src.f.flags ${prev} M, M) := by
  have hm : withCarried src M κ = M := by funext i j; rfl
  have hv : decideQ src ${prev} M = ${prev} := by funext i; simp [decideQ_of, src, lookup]
  simp only [sView, hm]
  change (decideFlags src.f.flags (decideQ src (before ρ ι) M) M, M) = _
  rw [hv]

theorem assume_eq ${stepvars}
    (h : evalC (sView src ρ M ι κ).1 (sView src ρ M ι κ).2 src.f.m.assume = true) :
    holdsC ${prev} M (${t.c(locals[0]!.assumptions[0]!)}) := by
  rw [view_eq] at h
  simpa [${sem}] using h

theorem bound_next ${stepvars} : ${next}.1 ${boundIx} = ρ ${boundIx} := by
  simp only [sNext, view_eq, Prod.fst, Prod.snd]
  simp [${sem}]

theorem bound_before (ρ ι : Nat → Nat) : ${prev} ${boundIx} = ρ ${boundIx} := by rfl
${certs}

theorem coupled_init (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hm : StartMaps src.f.m M) :
    Coupled (applyS src.f.m.init ρ M) M := by
  have hMap (j : Nat) : M 0 j = ${m.maps![p.map]} := hm (0,${m.maps![p.map]}) (by simp [src]) j
  unfold Coupled
  refine ⟨${p.fields.map(()=>'?_').join(', ')}⟩
${p.fields.map(bindStep).join('')}

theorem coupled_next ${stepvars}
    (hold : Coupled ρ M) (adm : evalC (sView src ρ M ι κ).1 (sView src ρ M ι κ).2 src.f.m.assume = true) :
    Coupled ${next}.1 ${next}.2 := by
  let X := before ρ ι
  let N := ρ ${boundIx}
  let q := point X M
  let ρ' := ${next}.1
  let M' := ${next}.2
  have hn : ρ' ${boundIx} = N := bound_next ρ M ι κ
  have hb : X ${boundIx} = N := bound_before ρ ι
  have ha := assume_eq ρ M ι κ adm
  have hq : q < N := by simpa only [q, point, holdsC, evalE, hb] using checked_point_inside X M ha
  have haAt (j : Nat) : holdsC ${shift('j')} M (${t.c(locals[1]!.assumptions[0]!)}) := by
    simpa [holdsC, evalE, upd] using ha
  have hqAt (j : Nat) : point ${shift('j')} M = q := by simp [point, evalE, upd, q]
  obtain ⟨${p.fields.map((_,i)=>`hold${i}`).join(', ')}⟩ := hold
  change Coupled ρ' M'
  unfold Coupled
  rw [hn]
  by_cases hr : holdsC X M (${t.c(p.reset)})
  · have hrAt (j : Nat) : holdsC ${shift('j')} M (${t.c(p.reset)}) := by simpa [holdsC, evalE, upd] using hr
    have resetMap (j : Nat) : M' 0 ${addr('j')} = ${m.maps![p.map]} := by
      have v := checked_broadcast_reset ${shift('j')} M (haAt j) (hrAt j)
      simp only [M', sNext, view_eq, Prod.fst, Prod.snd]
      simpa [X, ${sem}] using v
    refine ⟨${p.fields.map(()=>'?_').join(', ')}⟩
${p.fields.map((f,i)=>`    · have hz : ρ' ${ix(f.field)} = 0 := by
        simp only [ρ', sNext, view_eq, Prod.fst, Prod.snd]
        simpa [X, ${sem}] using checked_field${i}_reset X M ha hr
      rw [hz]
      apply Eq.symm
      exact zeroSum _ _ (by intro j; simp [countCell, resetMap])`).join('\n')}
  · have hrAt (j : Nat) : ¬holdsC ${shift('j')} M (${t.c(p.reset)}) := by simpa [holdsC, evalE, upd] using hr
    have frameMap (j : Nat) (hne : j ≠ q) : M' 0 ${addr('j')} = M 0 ${addr('j')} := by
      have hneq : holdsC ${shift('j')} M (${t.c(locals[1]!.assumptions[2]!)}) := by
        change (j ≠ point ${shift('j')} M)
        rwa [hqAt]
      have v := checked_other_cells_frame ${shift('j')} M (haAt j) (hrAt j) hneq
      simp only [M', sNext, view_eq, Prod.fst, Prod.snd]
      simpa [X, ${sem}] using v
    refine ⟨${p.fields.map(()=>'?_').join(', ')}⟩
${p.fields.map((f,i)=>`    · have delta : ρ' ${ix(f.field)} + countCell ${f.value} M q = ρ ${ix(f.field)} + countCell ${f.value} M' q := by
        simp only [ρ', M', countCell, sNext, view_eq, Prod.fst, Prod.snd]
        simpa [q, point, X, ${sem}] using checked_field${i}_delta X M ha hr
      exact coupled_change _ _ _ _ _ _ hq (by intro j _ hne; simp [countCell, frameMap j hne]) hold${i} delta`).join('\n')}

theorem all_coupled {ρ M} (h : SReach src ρ M) : Coupled ρ M := by
  induction h with
  | start ρ M hm _ _ _ => exact coupled_init ρ M hm
  | step ρ M ι κ _ adm ih => exact coupled_next ρ M ι κ ih adm

theorem original_law {ρ M} (h : SReach src ρ M) : holdsC ρ M original := by
  obtain ⟨${p.fields.map((_,i)=>`hold${i}`).join(', ')}⟩ := all_coupled h
  apply checked_capacity_entails_claim
  change ${cap} ≤ ρ ${boundIx}
  rw [${p.fields.map((_,i)=>`hold${i}`).join(', ')}]
  rw [${p.fields.slice(1).map(()=> '← sumBelow_add').join(', ')}]
  calc
    _ ≤ sumBelow (fun _ => 1) (ρ ${boundIx}) := by
      apply sumBelow_mono
      intro j _
      have v := checked_disjoint_capacity (upd ρ ${ix(coordinate)} j) M
      change ${classBody('M')} ≤ 1
      simpa [countCell, holdsC, evalE, evalC, upd] using v
    _ = ρ ${boundIx} := by simp [sumBelow_const]

theorem aggregate_claim : ∀ ρ M, SReach src ρ M → holdsC ρ M original :=
  fun _ _ h => original_law h
`
}
