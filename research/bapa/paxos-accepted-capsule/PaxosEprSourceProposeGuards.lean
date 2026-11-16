import PaxosEprAtomicGuards
namespace Bapa.PaxosEprAtomicSource
open Kern
namespace Propose
noncomputable def qView (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :=
 decideQ machine (withInputs machine.f.m.inputs ρ ι) (withCarried machine M κ)

theorem q_input (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (i : Nat) (hi : i ∈ [4,5,6,7,8,9]) : qView ρ M ι κ i = ι i := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [qView,decideQ,machine,lookup,withInputs]

theorem q_static (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (i : Nat) (hi : i ∈ [0,1,2,3]) : qView ρ M ι κ i = ρ i := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl | rfl | rfl | rfl <;>
  simp [qView,decideQ,machine,lookup,withInputs]

theorem v_input (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (i : Nat) (hi : i ∈ [4,5,6,7,8,9]) : (sView machine ρ M ι κ).1 i = ι i := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [sView,decideFlags,applyS,flagSub,assoc,lookup,decideQ,machine,withInputs]

theorem v_static (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (i : Nat) (hi : i ∈ [0,1,2,3]) : (sView machine ρ M ι κ).1 i = ρ i := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl | rfl | rfl | rfl <;>
  simp [sView,decideFlags,applyS,flagSub,assoc,lookup,decideQ,machine,withInputs]

theorem v_quantified (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (i : Nat) (hi : i ∈ [11,12,13,19]) : (sView machine ρ M ι κ).1 i = qView ρ M ι κ i := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl | rfl | rfl | rfl <;>
  simp [sView,qView,decideFlags,applyS,flagSub,assoc,lookup,machine]

private theorem code_one {p : Prop} [Decidable p] (h : (if p then (1:Nat) else 0) = 1) : p := by
 by_cases hp : p
 · exact hp
 · simp only [if_neg hp] at h
   contradiction

private theorem dec_true {p : Prop} [inst : Decidable p] : decide p = true ↔ p := by
 cases inst with
 | isTrue hp => exact ⟨fun _ => hp, fun _ => rfl⟩
 | isFalse hp => constructor; intro h; cases h; intro h; exact (hp h).elim
private theorem dec_false {p : Prop} [inst : Decidable p] : decide p = false ↔ ¬ p := by
 cases inst with
 | isTrue hp => constructor; intro h; cases h; intro h; exact (h hp).elim
 | isFalse hp => exact ⟨fun _ => hp, fun _ => rfl⟩

theorem plain_guard (D : Nat → Nat) (N : Nat → Nat → Nat)
 (h : decideFlags machine.f.flags D N 16 = 1) :
 D 4 = 2 ∧ D 6 ≠ D 3 ∧ D 11 = 1 ∧ D 12 = 1 ∧ D 13 = 1 ∧
 (D 8 = D 3 ∨ (1 ≤ N 6 (D 9) ∧ D 8 < D 6 ∧ 1 ≤ N 4 (cpair (D 9) (cpair (D 8) (D 7))))) := by
 have hx := h
 simp only [decideFlags,applyS,flagSub,assoc,lookup,machine,evalE] at hx
 have ht := code_one hx
 simp [evalC,evalE] at ht
 obtain ⟨ho,hr,hn,hj,hrow,hmax⟩ := ht
 refine ⟨of_decide_eq_true ho,dec_false.mp hr,of_decide_eq_true hn,
  of_decide_eq_true hj,of_decide_eq_true hrow,?_⟩
 rcases hmax with hnone | ⟨hq,hl,hv⟩
 · exact .inl (of_decide_eq_true hnone)
 · exact .inr ⟨of_decide_eq_true hq,of_decide_eq_true hl,of_decide_eq_true hv⟩

theorem actual_guard (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (h : (sView machine ρ M ι κ).1 16 = 1) :
 ι 4 = 2 ∧ ι 6 ≠ ρ 3 ∧ (sView machine ρ M ι κ).1 11 = 1 ∧
 (sView machine ρ M ι κ).1 12 = 1 ∧ (sView machine ρ M ι κ).1 13 = 1 ∧
 (ι 8 = ρ 3 ∨ (1 ≤ κ 6 (ι 9) ∧ ι 8 < ι 6 ∧ 1 ≤ M 4 (cpair (ι 9) (cpair (ι 8) (ι 7))))) := by
 have hx := plain_guard (qView ρ M ι κ) (withCarried machine M κ) h
 have n4 : withCarried machine M κ 4 = M 4 := rfl
 have n6 : withCarried machine M κ 6 = κ 6 := rfl
 simpa only [q_input ρ M ι κ 4 (by decide),q_input ρ M ι κ 6 (by decide),
  q_input ρ M ι κ 7 (by decide),q_input ρ M ι κ 8 (by decide),q_input ρ M ι κ 9 (by decide),
  q_static ρ M ι κ 3 (by decide),←v_quantified ρ M ι κ 11 (by decide),
  ←v_quantified ρ M ι κ 12 (by decide),←v_quantified ρ M ι κ 13 (by decide),n4,n6] using hx

theorem admission_view (D : Nat → Nat) (N : Nat → Nat → Nat) (hop : D 4 = 2)
 (h : evalC D N machine.f.m.assume = true) :
 D 5 < D 0 ∧ D 9 < D 0 ∧ D 19 = 1 ∧ D 0 < 2 * N 7 0 := by
 simp [machine,evalC,evalE,hop] at h
 obtain ⟨hn,hw,_,_,_,hq,hm⟩ := h
 refine ⟨of_decide_eq_true hn,of_decide_eq_true hw,of_decide_eq_true hq,?_⟩
 first | exact of_decide_eq_true hm | exact hm

theorem actual_admission (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (hop : ι 4 = 2) (h : evalC (sView machine ρ M ι κ).1 (sView machine ρ M ι κ).2 machine.f.m.assume = true) :
 ι 5 < ρ 0 ∧ ι 9 < ρ 0 ∧ (sView machine ρ M ι κ).1 19 = 1 ∧ ρ 0 < 2 * κ 7 0 := by
 have op : (sView machine ρ M ι κ).1 4 = 2 := (v_input ρ M ι κ 4 (by decide)).trans hop
 have hx := admission_view _ _ op h
 have n7 : (sView machine ρ M ι κ).2 7 = κ 7 := rfl
 simpa only [v_input ρ M ι κ 5 (by decide),v_input ρ M ι κ 9 (by decide),v_static ρ M ι κ 0 (by decide),n7] using hx

#print axioms plain_guard
#print axioms actual_guard
#print axioms actual_admission
end Propose
end Bapa.PaxosEprAtomicSource
