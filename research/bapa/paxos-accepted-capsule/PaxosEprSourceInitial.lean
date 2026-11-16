import PaxosEprSourceProposeEffect
namespace Bapa.PaxosEprSourceScan
open Kern Bapa.FiniteSimulation

def initialEnv (ρ : Nat → Nat) : Nat → Nat := fun i => if i = 0 then ρ 3 else if i = 1 then ρ 0 else 0

theorem initial_from_maps (ρ : Nat → Nat) (M : Nat → Nat → Nat)
 (hm : StartMaps PaxosEprAtomicSource.machine.f.m M) :
 ∃ y, Initial PaxosEprTarget.machine y ∧ Idle (atomicStore ρ M) y := by
 let Z : Nat → Nat → Nat := fun _ _ => 0
 let E := initialEnv ρ
 let y : KState := (applyS PaxosEprTarget.machine.f.m.init E Z,Z)
 have mz : StartMaps PaxosEprTarget.machine.f.m Z := by
  simp [StartMaps,PaxosEprTarget.machine,Z]
 have publicZero (mp : Nat) (hmp : mp < 6) (key : Nat) : M mp key = 0 := by
  have cases : mp=0 ∨ mp=1 ∨ mp=2 ∨ mp=3 ∨ mp=4 ∨ mp=5 := by omega
  have hmem : (mp,0) ∈ PaxosEprAtomicSource.machine.f.m.maps0 := by
   rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  exact hm (mp,0) hmem key
 refine ⟨y,⟨E,Z,mz,rfl,?_,?_,rfl⟩,?_⟩
 · simp [PaxosEprTarget.machine]
 · simp [SMachine.PFacts,PaxosEprTarget.machine]
 · refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
   · intro mp hmp key
     exact (publicZero mp hmp key).symm
   · intro key
     rfl

theorem source_initial_matches (x : KState) (h : Initial PaxosEprAtomicSource.machine x) :
 ∃ y, Reachable (Initial PaxosEprTarget.machine)
   (CTransition PaxosEprTarget.machine PaxosEprTarget.declarations) y ∧ Idle (atomicStore x.1 x.2) y := by
 obtain ⟨ρ,M,hm,_,_,_,rfl⟩ := h
 obtain ⟨y,hy,rel⟩ := initial_from_maps ρ M hm
 exact ⟨y,.initial hy,rel⟩

#print axioms initial_from_maps
#print axioms source_initial_matches
end Bapa.PaxosEprSourceScan
