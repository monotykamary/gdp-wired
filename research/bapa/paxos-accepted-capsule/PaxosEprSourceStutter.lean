import PaxosEprSourceInitial
namespace Bapa.PaxosEprAtomicSource.Propose
open Kern

theorem inactive_public (V : Nat → Nat) (N : Nat → Nat → Nat) (hb : BooleanMaps N)
 (h14 : V 14 = 0) (h15 : V 15 = 0) (h16 : V 16 ≠ 1) (h17 : V 17 = 0) (h18 : V 18 = 0) :
 ∀ mp, mp < 6 → ∀ key, everyMaps machine V N mp key = N mp key := by
 have he (mp) (hm : mp < 6) (key) : (if decide (N mp key = 1) = true then 1 else 0) = N mp key := by
  have h := hb mp hm key
  have cases : N mp key = 0 ∨ N mp key = 1 := by omega
  rcases cases with h | h <;> simp [h]
 have kr (key : Nat) : cpair (pickP 0 key) (pickP 1 key) = key := by simp [pickP]
 intro mp hm key
 have cases : mp=0 ∨ mp=1 ∨ mp=2 ∨ mp=3 ∨ mp=4 ∨ mp=5 := by omega
 rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
 · by_cases hk : key = V 6 <;>
    simp [everyMaps,machine,lookup,writeMaps,evalE,evalC,h14,hk] <;> exact he _ (by decide) _
 · by_cases hk : key = cpair (V 6) (V 5) <;>
    simp [everyMaps,machine,lookup,writeMaps,evalE,evalC,h15,hk]
 · simp [everyMaps,machine,lookup,evalE,evalC,upd,h15,kr]
   have h := hb 2 (by decide) key
   have cases : N 2 key = 0 ∨ N 2 key = 1 := by omega
   rcases cases with h | h <;> simp [h]
 · by_cases hk : key = cpair (V 6) (V 7) <;>
    simp [everyMaps,machine,lookup,writeMaps,evalE,evalC,h16,hk]
 · by_cases hk : key = cpair (V 5) (cpair (V 6) (V 7)) <;>
    simp [everyMaps,machine,lookup,writeMaps,evalE,evalC,h17,hk]
 · by_cases hk : key = cpair (V 6) (V 7) <;>
    simp [everyMaps,machine,lookup,writeMaps,evalE,evalC,h18,hk]

theorem disabled_public_effect {ρ M} (reach : CReach machine declarations ρ M)
 (ι : Nat → Nat) (κ : Nat → Nat → Nat) (hop : ι 4 = 2)
 (hp : (sView machine ρ M ι κ).1 16 ≠ 1) :
 ∀ mp, mp < 6 → ∀ key, (sNext machine ρ M ι κ).2 mp key = M mp key := by
 obtain ⟨h14,h15,h17,h18⟩ := other_flags ρ M ι κ hop
 have low (mp : Nat) (hm : mp < 6) : withCarried machine M κ mp = M mp := by
  have cases : mp=0 ∨ mp=1 ∨ mp=2 ∨ mp=3 ∨ mp=4 ∨ mp=5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
 have nb : BooleanMaps (withCarried machine M κ) := by
  intro mp hm key
  rw [low mp hm]
  exact counted_reachable_boolean reach mp hm key
 intro mp hm key
 have h := inactive_public (sView machine ρ M ι κ).1 (withCarried machine M κ) nb h14 h15 hp h17 h18 mp hm key
 simp only [low mp hm] at h
 simpa only [sNext,sView] using h
#print axioms disabled_public_effect
end Bapa.PaxosEprAtomicSource.Propose

namespace Bapa.PaxosEprSourceScan
open Kern Bapa.FiniteSimulation

theorem matched_disabled_propose {ρ : Nat → Nat} {M : Nat → Nat → Nat}
 (reach : CReach PaxosEprAtomicSource.machine PaxosEprAtomicSource.declarations ρ M)
 (ι : Nat → Nat) (κ : Nat → Nat → Nat) (hop : ι 4 = 2)
 (hp : (sView PaxosEprAtomicSource.machine ρ M ι κ).1 16 ≠ 1)
 {x : KState} (hx : Idle (atomicStore ρ M) x) :
 ∃ y, CSteps PaxosEprTarget.machine PaxosEprTarget.declarations x y ∧
  Idle (atomicStore (sNext PaxosEprAtomicSource.machine ρ M ι κ).1 (sNext PaxosEprAtomicSource.machine ρ M ι κ).2) y := by
 have ne := PaxosEprAtomicSource.Propose.static_next ρ M ι κ 3 (by decide)
 have se := PaxosEprAtomicSource.Propose.static_next ρ M ι κ 0 (by decide)
 have pe := PaxosEprAtomicSource.Propose.disabled_public_effect reach ι κ hop hp
 refine ⟨x,.refl _,?_,?_,hx.busy,hx.count,hx.round,hx.maxRound,hx.value,?_,hx.quorum⟩
 · exact hx.none.trans ne.symm
 · exact hx.size.trans se.symm
 · intro mp hm key
   exact (hx.publicMaps mp hm key).trans (pe mp hm key).symm
theorem matched_propose {ρ : Nat → Nat} {M : Nat → Nat → Nat}
 (reach : CReach PaxosEprAtomicSource.machine PaxosEprAtomicSource.declarations ρ M)
 (ι : Nat → Nat) (κ : Nat → Nat → Nat) (hop : ι 4 = 2)
 (hg : GHolds PaxosEprAtomicSource.declarations
   (withInputs PaxosEprAtomicSource.machine.f.m.inputs ρ ι) (withCarried PaxosEprAtomicSource.machine M κ))
 (ha : evalC (sView PaxosEprAtomicSource.machine ρ M ι κ).1 (sView PaxosEprAtomicSource.machine ρ M ι κ).2 PaxosEprAtomicSource.machine.f.m.assume = true)
 {x : KState} (hx : Idle (atomicStore ρ M) x) :
 ∃ y, CSteps PaxosEprTarget.machine PaxosEprTarget.declarations x y ∧
  Idle (atomicStore (sNext PaxosEprAtomicSource.machine ρ M ι κ).1 (sNext PaxosEprAtomicSource.machine ρ M ι κ).2) y := by
 by_cases hp : (sView PaxosEprAtomicSource.machine ρ M ι κ).1 16 = 1
 · exact matched_source_propose reach ι κ hg ha hp hx
 · exact matched_disabled_propose reach ι κ hop hp hx

#print axioms matched_propose
#print axioms matched_disabled_propose
end Bapa.PaxosEprSourceScan
