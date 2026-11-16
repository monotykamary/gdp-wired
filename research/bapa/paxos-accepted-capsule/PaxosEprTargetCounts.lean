import PaxosEprTargetDefs
import FiniteSimulation
namespace Bapa.PaxosEprTarget
open Kern Bapa.FiniteSimulation

/-- Real count maps exist for every concrete target request. Non-count maps,
including the carried quorum, are preserved. No arbitrary GHolds assumption. -/
theorem realize_counts (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    ∃ κ', (∀ mp, mp ∉ cMaps declarations →
      withCarried machine M κ' mp = withCarried machine M κ mp) ∧
      GHolds declarations (withInputs machine.f.m.inputs ρ ι) (withCarried machine M κ') := by
  apply counts_exist machine declarations
  · decide +kernel
  · intro d hd
    simp only [declarations, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro d hd
    simp only [declarations, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- A concrete request whose admission is established after count realization
is an actual counted edge, not merely an uncounted transition. -/
theorem counted_edge {ρ M ι κ}
    (hg : GHolds declarations (withInputs machine.f.m.inputs ρ ι) (withCarried machine M κ))
    (ha : evalC (sView machine ρ M ι κ).1 (sView machine ρ M ι κ).2 machine.f.m.assume = true) :
    CTransition machine declarations (ρ,M) (sNext machine ρ M ι κ) := ⟨ι,κ,hg,ha,rfl⟩

#print axioms realize_counts
#print axioms counted_edge
end Bapa.PaxosEprTarget
