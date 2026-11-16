import PaxosEprSourceProposeScan
namespace Bapa.PaxosEprAtomicSource.Propose
open Kern

private theorem code_eq {n : Nat} (h : n ≤ 1) : (if decide (n = 1) = true then 1 else 0) = n := by
 have hn : n = 0 ∨ n = 1 := by omega
 rcases hn with rfl | rfl <;> rfl
private theorem code_ge {n : Nat} (h : n ≤ 1) : (if decide (1 ≤ n) = true then 1 else 0) = n := by
 have hn : n = 0 ∨ n = 1 := by omega
 rcases hn with rfl | rfl <;> rfl

theorem other_flags (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (hop : ι 4 = 2) :
 let V := (sView machine ρ M ι κ).1
 V 14 = 0 ∧ V 15 = 0 ∧ V 17 = 0 ∧ V 18 = 0 := by
 simp [sView,machine,decideFlags,applyS,flagSub,assoc,lookup,decideQ,withInputs,evalE,evalC,hop]

theorem public_effect (V : Nat → Nat) (N : Nat → Nat → Nat) (hb : BooleanMaps N)
 (h14 : V 14 = 0) (h15 : V 15 = 0) (h16 : V 16 = 1) (h17 : V 17 = 0) (h18 : V 18 = 0) :
 ∀ mp, mp < 6 → ∀ key, everyMaps machine V N mp key =
   if mp = 3 ∧ key = cpair (V 6) (V 7) then 1 else N mp key := by
 have he (mp) (hm : mp < 6) (key) := code_eq (hb mp hm key)
 have hg (mp) (hm : mp < 6) (key) := code_ge (hb mp hm key)
 have kr (key : Nat) : cpair (pickP 0 key) (pickP 1 key) = key := by simp [pickP,cpair_cun]
 intro mp hm key
 have cases : mp=0 ∨ mp=1 ∨ mp=2 ∨ mp=3 ∨ mp=4 ∨ mp=5 := by omega
 rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
 · by_cases hk : key = V 6 <;>
    simp [everyMaps,machine,lookup,writeMaps,evalE,evalC,h14,hk,he] <;> exact he _ (by decide) _
 · by_cases hk : key = cpair (V 6) (V 5) <;>
    simp [everyMaps,machine,lookup,writeMaps,evalE,evalC,h15,hk]
 · simp [everyMaps,machine,lookup,evalE,evalC,upd,h15,kr,hg]
   have h := hb 2 (by decide) key
   have cases : N 2 key = 0 ∨ N 2 key = 1 := by omega
   rcases cases with h | h <;> simp [h]
 · by_cases hk : key = cpair (V 6) (V 7) <;>
    simp [everyMaps,machine,lookup,writeMaps,evalE,evalC,h16,hk]
 · by_cases hk : key = cpair (V 5) (cpair (V 6) (V 7)) <;>
    simp [everyMaps,machine,lookup,writeMaps,evalE,evalC,h17,hk]
 · by_cases hk : key = cpair (V 6) (V 7) <;>
    simp [everyMaps,machine,lookup,writeMaps,evalE,evalC,h18,hk]

theorem actual_public_effect {ρ M} (reach : CReach machine declarations ρ M)
 (ι : Nat → Nat) (κ : Nat → Nat → Nat) (hp : (sView machine ρ M ι κ).1 16 = 1) :
 ∀ mp, mp < 6 → ∀ key, (sNext machine ρ M ι κ).2 mp key =
   if mp = 3 ∧ key = cpair (ι 6) (ι 7) then 1 else M mp key := by
 have hop := (actual_guard ρ M ι κ hp).1
 obtain ⟨h14,h15,h17,h18⟩ := other_flags ρ M ι κ hop
 have low (mp : Nat) (hm : mp < 6) : withCarried machine M κ mp = M mp := by
  have cases : mp=0 ∨ mp=1 ∨ mp=2 ∨ mp=3 ∨ mp=4 ∨ mp=5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
 have nb : BooleanMaps (withCarried machine M κ) := by
  intro mp hm key
  rw [low mp hm]
  exact counted_reachable_boolean reach mp hm key
 intro mp hm key
 have h := public_effect (sView machine ρ M ι κ).1 (withCarried machine M κ) nb h14 h15 hp h17 h18 mp hm key
 simp only [v_input ρ M ι κ 6 (by decide),v_input ρ M ι κ 7 (by decide),low mp hm] at h
 simpa only [sNext,sView] using h

theorem static_next (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (i : Nat) (hi : i ∈ [0,1,2,3]) : (sNext machine ρ M ι κ).1 i = ρ i := by
 change (sView machine ρ M ι κ).1 i = ρ i
 exact v_static ρ M ι κ i hi

#print axioms actual_public_effect
#print axioms static_next
end Bapa.PaxosEprAtomicSource.Propose

namespace Bapa.PaxosEprSourceScan
open Kern Bapa.FiniteSimulation
/-- The enabled source Propose is matched to its ACTUAL post-state, not just
an informal insertion specification. Other source operations are separate. -/
theorem matched_source_propose {ρ : Nat → Nat} {M : Nat → Nat → Nat}
 (reach : CReach PaxosEprAtomicSource.machine PaxosEprAtomicSource.declarations ρ M)
 (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (hg : GHolds PaxosEprAtomicSource.declarations
   (withInputs PaxosEprAtomicSource.machine.f.m.inputs ρ ι) (withCarried PaxosEprAtomicSource.machine M κ))
 (ha : evalC (sView PaxosEprAtomicSource.machine ρ M ι κ).1 (sView PaxosEprAtomicSource.machine ρ M ι κ).2 PaxosEprAtomicSource.machine.f.m.assume = true)
 (hp : (sView PaxosEprAtomicSource.machine ρ M ι κ).1 16 = 1)
 {x : KState} (hx : Idle (atomicStore ρ M) x) :
 ∃ y, CSteps PaxosEprTarget.machine PaxosEprTarget.declarations x y ∧
  Idle (atomicStore (sNext PaxosEprAtomicSource.machine ρ M ι κ).1 (sNext PaxosEprAtomicSource.machine ρ M ι κ).2) y := by
 obtain ⟨y,path,done⟩ := source_propose_scans reach ι κ hg ha hp hx
 have ne := PaxosEprAtomicSource.Propose.static_next ρ M ι κ 3 (by decide)
 have se := PaxosEprAtomicSource.Propose.static_next ρ M ι κ 0 (by decide)
 have pe := PaxosEprAtomicSource.Propose.actual_public_effect reach ι κ hp
 refine ⟨y,path,?_,?_,done.busy,done.count,done.round,done.maxRound,done.value,?_,done.quorum⟩
 · change y.1 0 = (sNext PaxosEprAtomicSource.machine ρ M ι κ).1 3
   exact done.none.trans ne.symm
 · change y.1 1 = (sNext PaxosEprAtomicSource.machine ρ M ι κ).1 0
   exact done.size.trans se.symm
 · intro mp hm key
   change y.2 mp key = (sNext PaxosEprAtomicSource.machine ρ M ι κ).2 mp key
   exact (done.publicMaps mp hm key).trans (pe mp hm key).symm

#print axioms matched_source_propose
end Bapa.PaxosEprSourceScan
