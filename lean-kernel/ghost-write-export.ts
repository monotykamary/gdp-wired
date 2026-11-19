import type {Law,Machine} from '../core/machine.ts'
import {checkGhostWrite,ghostWriteTheory,type GhostWriteCertificate} from '../kernel/ghost-write.ts'
import {plainOf} from '../kernel/kernel.ts'
import {seedStepProof,smachineToLean} from './emit.ts'

export function ghostWriteToLean(id:string,source:Machine,law:Law,p:GhostWriteCertificate):string {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(id) || !checkGhostWrite(source,law,p)) throw Error('invalid ghost-write export')
  const {target,laws,orig,publicEntry}=ghostWriteTheory(source,law,p)!, r=p.recipe
  // The exact retained family only. A proof producer is not run at export.
  seedStepProof(plainOf(target),laws,[],{proven:true,checked:true,nodes:0,leaves:0,proof:{laws:p.proof,instances:{},perStep:{},trees:{}}})
  const body=smachineToLean('packet',target,laws,{free:[law.forall!],coverTrees:p.proof.trees,after:(ix,mx,lit,cond)=>{
    const binder=Object.entries(orig.step.flags??{}).map(([f,a])=>{
      if (a.op!=='all') throw Error('expected closed flag')
      return `if i = ${ix(`?${f}`)} then ${ix(a.key)} else `
    }).join('')+'0'
    const goal=cond(law.holds), specialization=cond(laws[publicEntry]!.holds)
    const ghost=mx(r.ghostMap), observer=ix(r.observer)
    const declared=Object.keys(source.maps??{}).map(mx).join(',')
    return `
def originalMachine : SMachine := ${lit(source)}
def unchangedLaw : MLaw := ⟨${goal}, some ${ix(law.forall!)}⟩
def observer : Nat := ${observer}
def ghostMap : Nat := ${ghost}
def closedBinder (i : Nat) : Nat := ${binder}
def closedSource : SMachine := ${lit(orig)}
def pointIndex : E := ((packet_sums.s.f.m.writes.find? (fun row => row.1 == ghostMap)).map (fun row => row.2.1)).getD (.const 0)
def recipe : GhostWrite.Recipe := ⟨pointIndex, [${r.gates.map(([m,v])=>`(${mx(m)}, ${v})`).join(',')}], ${mx(r.group)}, ${mx(r.weight)}, observer⟩
def sourceMapIds : List Nat := [${declared}]
def closedPoint : GhostWrite.Point := GhostWrite.completePoint closedSource ghostMap recipe

theorem recipeChecks : GhostWrite.Checked closedSource sourceMapIds ghostMap recipe := by
  constructor <;> first | rfl | decide +kernel

theorem targetShape : packet_sums.s = (GhostWrite.aug closedSource closedPoint).full := by rfl
theorem sumGhostChecks : sghostOk packet_sums.ghosts = true := by decide +kernel
theorem promotionIdentity : closedSource = GhostSourceViews.promote originalMachine closedBinder closedSource.wits := by rfl

def specialized : C := ${specialization}
def projectedLaw (v : GhostWrite.Env × ({m : Nat // m ≠ ghostMap} → GhostWrite.Env)) : Prop :=
  holdsC v.1 (fun m => if h : m ≠ ghostMap then v.2 ⟨m,h⟩ else fun _ => 0) specialized

theorem projectedLaw_iff (y : GhostWrite.State) :
    projectedLaw (GhostWrite.projection closedPoint y) ↔ evalC y.1 y.2 specialized = true := by
  unfold projectedLaw
  rw [← evalC_iff]
  change evalC y.1 (fun m => if _ : m ≠ ghostMap then y.2 m else fun _ => 0) specialized = true ↔ _
  have hm : avoidsMaps [ghostMap] specialized = true := by decide +kernel
  rw [congrMC y.1 _ y.2 specialized]
  intro m occurs
  have h : m ≠ ghostMap := by simpa using avoidsMaps_occ hm occurs
  simp [h]

theorem original_law (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (hr : SReach originalMachine ρ M) : unchangedLaw.Holds ρ M := by
  intro k
  have ho := GhostSourceViews.source_rebind originalMachine observer rfl rfl rfl (by decide +kernel) hr k
  have hc : SReach closedSource (upd ρ observer k) M :=
    (GhostSourceViews.candidate_reach closedBinder _ promotionIdentity rfl (by decide +kernel)).mpr ho
  have hinv (y : GhostWrite.State) (hy : SReach packet_sums.s y.1 y.2) :
      projectedLaw (GhostWrite.projection closedPoint y) := by
    apply (projectedLaw_iff y).mpr
    exact sum_project_laws packet_sums sumGhostChecks packet_proof packet_check packet_scheck
      y.1 y.2 hy packet_e${publicEntry} (by simp [packet_proof]) (by decide +kernel)
  have hp := GhostWrite.checkedTransport recipeChecks packet_sums.s targetShape projectedLaw hinv hc
  have hl := (projectedLaw_iff (upd ρ observer k,M)).mp hp
  change evalC (upd ρ ${ix(law.forall!)} k) M (${goal}) = true
  simpa [specialized, observer, evalC, evalE, upd] using hl

#print axioms packet_check
#print axioms packet_scheck
#print axioms recipeChecks
#print axioms original_law
`
  }})
  return `namespace ${id}
open Kern Cert Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 0
${body}
end ${id}\n`
}
