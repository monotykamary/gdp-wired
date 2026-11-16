import PaxosEprTargetQuorum
import PaxosEprTargetState
namespace Bapa.PaxosEprTarget
open Kern Bapa.FiniteSimulation

def startInput (n r v mr w : Nat) : Nat → Nat := fun i =>
  match i with
  | 2 => 2 | 3 => n | 4 => r | 5 => v | 6 => mr | 7 => w | _ => 0

theorem view_input (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (i : Nat) (hi : i ∈ [2,3,4,5,6,7]) :
    (sView machine ρ M ι κ).1 i = ι i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sView,decideFlags,applyS,flagSub,assoc,lookup,decideQ,machine,withInputs]

theorem noProposal_flag (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hn : ∀ v, M 3 (cpair (ι 4) v) ≠ 1) : (sView machine ρ M ι κ).1 70 = 1 := by
  classical
  have h : ∀ k : Nat → Nat, ¬ M 3 (cpair (ι 4) (k 131)) = 1 := fun k => hn _
  have he : (if ∀ k : Nat → Nat, ¬ M 3 (cpair (ι 4) (k 131)) = 1 then (1 : Nat) else 0) = 1 := by
    rw [if_pos h]
  simpa [sView,machine,decideFlags,applyS,flagSub,assoc,lookup,decideQ,
    withInputs,holdsC,evalE,atKeys,withCarried] using he

theorem joined_flag (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hj : ∀ n, 1 ≤ κ 7 n → M 1 (cpair (ι 4) n) = 1) : (sView machine ρ M ι κ).1 71 = 1 := by
  classical
  have h : ∀ k : Nat → Nat, ¬ 1 ≤ κ 7 (k 132) ∨ M 1 (cpair (ι 4) (k 132)) = 1 := by
    intro k
    by_cases hq : 1 ≤ κ 7 (k 132)
    · exact .inr (hj _ hq)
    · exact .inl hq
  have he : (if ∀ k : Nat → Nat, ¬ 1 ≤ κ 7 (k 132) ∨ M 1 (cpair (ι 4) (k 132)) = 1
      then (1 : Nat) else 0) = 1 := by rw [if_pos h]
  simpa [sView,machine,decideFlags,applyS,flagSub,assoc,lookup,decideQ,
    withInputs,holdsC,evalE,atKeys,withCarried] using he

theorem valid_quorum_flag (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hq : ∀ n, κ 7 n ≤ 1 ∧ (1 ≤ κ 7 n → n < ρ 1)) : (sView machine ρ M ι κ).1 81 = 1 := by
  classical
  have h : ∀ k : Nat → Nat, κ 7 (k 86) ≤ 1 ∧ (¬ 1 ≤ κ 7 (k 86) ∨ k 86 < ρ 1) := by
    intro k
    refine ⟨(hq _).1,?_⟩
    by_cases hp : 1 ≤ κ 7 (k 86)
    · exact .inr ((hq _).2 hp)
    · exact .inl hp
  have he : (if ∀ k : Nat → Nat, κ 7 (k 86) ≤ 1 ∧ (¬ 1 ≤ κ 7 (k 86) ∨ k 86 < ρ 1)
      then (1 : Nat) else 0) = 1 := by rw [if_pos h]
  simpa [sView,machine,decideFlags,applyS,flagSub,assoc,lookup,decideQ,
    withInputs,holdsC,evalE,atKeys,withCarried] using he

theorem start_plain_flags (D : Nat → Nat) (N : Nat → Nat → Nat)
    (hop : D 2 = 2) (hb : D 8 = 0) (hr : D 4 ≠ D 0)
    (hn : D 70 = 1) (hj : D 71 = 1)
    (hm : D 6 = D 0 ∨ (1 ≤ N 7 (D 7) ∧ D 6 < D 4 ∧ N 4 (cpair (D 7) (cpair (D 6) (D 5))) = 1)) :
    let V := decideFlags machine.f.flags D N
    V 73 = 0 ∧ V 74 = 0 ∧ V 75 = 1 ∧ V 76 = 0 ∧ V 77 = 0 ∧ V 78 = 0 ∧ V 79 = 0 ∧ V 80 = 0 := by
  rcases hm with hm | ⟨hq,hl,hv⟩
  · simp [decideFlags,machine,applyS,flagSub,assoc,lookup,evalE,evalC,hop,hb,hr,hn,hj,hm]
  · simp [decideFlags,machine,applyS,flagSub,assoc,lookup,evalE,evalC,hop,hb,hr,hn,hj,hq,hl,hv]

theorem start_view_admitted (D : Nat → Nat) (N : Nat → Nat → Nat)
    (hop : D 2 = 2) (hn : D 3 < D 1) (hw : D 7 < D 1)
    (hq : D 81 = 1) (hmaj : D 1 < 2 * N 8 0) : evalC D N machine.f.m.assume = true := by
  simp [machine,evalC,evalE,hop,hn,hw,hq,hmaj]

theorem start_admitted (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hop : ι 2 = 2) (hn : ι 3 < ρ 1) (hw : ι 7 < ρ 1)
    (hq : ∀ n, κ 7 n ≤ 1 ∧ (1 ≤ κ 7 n → n < ρ 1)) (hmaj : ρ 1 < 2 * κ 8 0) :
    evalC (sView machine ρ M ι κ).1 (sView machine ρ M ι κ).2 machine.f.m.assume = true := by
  apply start_view_admitted
  · simpa only [view_input ρ M ι κ 2 (by decide)] using hop
  · simpa only [view_input ρ M ι κ 3 (by decide),view_fixed ρ M ι κ 1 (by decide)] using hn
  · simpa only [view_input ρ M ι κ 7 (by decide),view_fixed ρ M ι κ 1 (by decide)] using hw
  · exact valid_quorum_flag ρ M ι κ hq
  · have hm : (sView machine ρ M ι κ).2 8 0 = κ 8 0 := by rfl
    simpa only [view_fixed ρ M ι κ 1 (by decide),hm] using hmaj

theorem start_counted_request (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (n r v mr w : Nat) (Q : Nat → Nat) (hn : n < ρ 1) (hw : w < ρ 1)
    (hq : ∀ k, Q k ≤ 1 ∧ (1 ≤ Q k → k < ρ 1)) (hmaj : ρ 1 < 2 * quorumCount (ρ 1) Q) :
    ∃ κ, κ 7 = Q ∧ CTransition machine declarations (ρ,M)
      (sNext machine ρ M (startInput n r v mr w) κ) := by
  obtain ⟨κ,hQ,hG,hC⟩ := realize_quorum ρ M (startInput n r v mr w) Q
  have ha := start_admitted ρ M (startInput n r v mr w) κ rfl hn hw
    (by simpa only [hQ] using hq) (by simpa only [hC] using hmaj)
  exact ⟨κ,hQ,counted_edge hG ha⟩

#print axioms noProposal_flag
#print axioms joined_flag
#print axioms valid_quorum_flag
#print axioms start_plain_flags
#print axioms start_admitted
#print axioms start_counted_request
end Bapa.PaxosEprTarget
