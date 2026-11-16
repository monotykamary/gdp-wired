import PaxosEprTargetStart
import PaxosEprConcreteWalk
namespace Bapa.PaxosEprTarget
open Kern Bapa.FiniteSimulation

theorem qView_input (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (i : Nat) (hi : i ∈ [2,3,4,5,6,7]) :
    qView ρ M ι κ i = ι i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [qView,decideQ,machine,lookup,withInputs]

theorem view_start_qflag (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (i : Nat) (hi : i = 70 ∨ i = 71) :
    (sView machine ρ M ι κ).1 i = qView ρ M ι κ i := by
  rcases hi with rfl | rfl <;>
    simp [sView,qView,decideFlags,applyS,flagSub,assoc,lookup,machine]

theorem start_actual_flags (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hop : ι 2 = 2) (hb : ρ 8 = 0) (hr : ι 4 ≠ ρ 0)
    (hn : ∀ v, M 3 (cpair (ι 4) v) ≠ 1)
    (hj : ∀ n, 1 ≤ κ 7 n → M 1 (cpair (ι 4) n) = 1)
    (hm : ι 6 = ρ 0 ∨ (1 ≤ κ 7 (ι 7) ∧ ι 6 < ι 4 ∧ M 4 (cpair (ι 7) (cpair (ι 6) (ι 5))) = 1)) :
    let V := (sView machine ρ M ι κ).1
    V 73 = 0 ∧ V 74 = 0 ∧ V 75 = 1 ∧ V 76 = 0 ∧ V 77 = 0 ∧ V 78 = 0 ∧ V 79 = 0 ∧ V 80 = 0 := by
  have qi (i) (hi : i ∈ [2,3,4,5,6,7]) := qView_input ρ M ι κ i hi
  have qf (i) (hi : FixedRegister i) := qView_fixed ρ M ι κ i hi
  have qn := noProposal_flag ρ M ι κ hn
  have qj := joined_flag ρ M ι κ hj
  rw [view_start_qflag ρ M ι κ 70 (.inl rfl)] at qn
  rw [view_start_qflag ρ M ι κ 71 (.inr rfl)] at qj
  have nc : withCarried machine M κ 7 = κ 7 := rfl
  have hp : qView ρ M ι κ 2 = 2 := (qi 2 (by decide)).trans hop
  have hbusy : qView ρ M ι κ 8 = 0 := (qf 8 (by decide)).trans hb
  have hround : qView ρ M ι κ 4 ≠ qView ρ M ι κ 0 := by
    simpa only [qi 4 (by decide),qf 0 (by decide)] using hr
  have hmax : qView ρ M ι κ 6 = qView ρ M ι κ 0 ∨
      (1 ≤ withCarried machine M κ 7 (qView ρ M ι κ 7) ∧
      qView ρ M ι κ 6 < qView ρ M ι κ 4 ∧
      withCarried machine M κ 4 (cpair (qView ρ M ι κ 7) (cpair (qView ρ M ι κ 6) (qView ρ M ι κ 5))) = 1) := by
    simpa only [qi 4 (by decide),qi 5 (by decide),qi 6 (by decide),qi 7 (by decide),
      qf 0 (by decide),nc,carried_low M κ 4 (by decide)] using hm
  have h := start_plain_flags (qView ρ M ι κ) (withCarried machine M κ) hp hbusy hround qn qj hmax
  simpa only [sView,qView] using h

theorem start_register_effect (V : Nat → Nat) (N : Nat → Nat → Nat)
    (h75 : V 75 = 1) (h76 : V 76 = 0) (h77 : V 77 = 0) (h78 : V 78 = 0) :
    let W := applyS machine.f.m.step V N
    W 0 = V 0 ∧ W 1 = V 1 ∧ W 8 = 1 ∧ W 9 = V 9 ∧
      W 10 = V 4 ∧ W 11 = V 6 ∧ W 12 = V 5 := by
  simp [machine,applyS,assoc,lookup,evalE,evalC,h75,h76,h77,h78]

theorem start_quorum_effect (V : Nat → Nat) (N : Nat → Nat → Nat)
    (h75 : V 75 = 1) (hq : ∀ k, N 7 k ≤ 1) (key : Nat) :
    everyMaps machine V N 6 key = N 7 key := by
  have cases : N 7 key = 0 ∨ N 7 key = 1 := by have := hq key; omega
  rcases cases with h | h <;>
    simp [everyMaps,machine,lookup,evalE,evalC,upd,h75,h]

theorem start_ready (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hop : ι 2 = 2) (hb : ρ 8 = 0) (hc : ρ 9 = 0) (hr : ι 4 ≠ ρ 0)
    (hn : ∀ v, M 3 (cpair (ι 4) v) ≠ 1)
    (hj : ∀ n, 1 ≤ κ 7 n → M 1 (cpair (ι 4) n) = 1)
    (hm : ι 6 = ρ 0 ∨ (1 ≤ κ 7 (ι 7) ∧ ι 6 < ι 4 ∧ M 4 (cpair (ι 7) (cpair (ι 6) (ι 5))) = 1))
    (hbool : BooleanSeven M) (hq : ∀ k, κ 7 k ≤ 1) :
    During ⟨ρ 1,ρ 0,M⟩ (κ 7) (ι 4) (ι 6) (ι 5) 0 (sNext machine ρ M ι κ) := by
  let V := (sView machine ρ M ι κ).1
  let N := withCarried machine M κ
  have vf (i : Nat) (hi : FixedRegister i) : V i = ρ i := view_fixed ρ M ι κ i hi
  have vi (i : Nat) (hi : i ∈ [2,3,4,5,6,7]) : V i = ι i := view_input ρ M ι κ i hi
  have nl (mp : Nat) (hm : mp < 7) : N mp = M mp := carried_low M κ mp hm
  have n7 : N 7 = κ 7 := rfl
  have hN : BooleanSeven N := by
    intro mp hm key
    rw [nl mp hm]
    exact hbool mp hm key
  obtain ⟨h73,h74,h75,h76,h77,h78,h79,h80⟩ := start_actual_flags ρ M ι κ hop hb hr hn hj hm
  obtain ⟨s0,s1,s8,s9,s10,s11,s12⟩ := start_register_effect V N h75 h76 h77 h78
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [vf 0 (by decide)] at s0
    simpa only [sNext,sView,V,N] using s0
  · simp only [vf 1 (by decide)] at s1
    simpa only [sNext,sView,V,N] using s1
  · simpa only [sNext,sView,V,N] using s8
  · simp only [vf 9 (by decide),hc] at s9
    simpa only [sNext,sView,V,N] using s9
  · simp only [vi 4 (by decide)] at s10
    simpa only [sNext,sView,V,N] using s10
  · simp only [vi 6 (by decide)] at s11
    simpa only [sNext,sView,V,N] using s11
  · simp only [vi 5 (by decide)] at s12
    simpa only [sNext,sView,V,N] using s12
  · intro mp hp key
    have h := scan_public_effect V N hN h73 h74 h79 h80 mp hp key
    have hz : V 78 = 0 := h78
    simp only [hz,show ¬ (0:Nat)=1 from by decide,and_false,false_and,if_false,nl mp (by omega)] at h
    simpa only [sNext,sView,V,N] using h
  · intro key
    have h := start_quorum_effect V N h75 (by simpa only [n7] using hq) key
    simpa only [sNext,sView,V,N,n7] using h

theorem encoded_start_step (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (n r v mr w : Nat) (Q : Nat → Nat)
    (hb : ρ 8 = 0) (hc : ρ 9 = 0) (hr : r ≠ ρ 0) (hbool : BooleanSeven M)
    (hn : n < ρ 1) (hw : w < ρ 1)
    (hq : ∀ k, Q k ≤ 1 ∧ (1 ≤ Q k → k < ρ 1)) (hmaj : ρ 1 < 2 * quorumCount (ρ 1) Q)
    (hnp : ∀ z, M 3 (cpair r z) ≠ 1)
    (hj : ∀ k, 1 ≤ Q k → M 1 (cpair r k) = 1)
    (hm : mr = ρ 0 ∨ (1 ≤ Q w ∧ mr < r ∧ M 4 (cpair w (cpair mr v)) = 1)) :
    ∃ y, CTransition machine declarations (ρ,M) y ∧ During ⟨ρ 1,ρ 0,M⟩ Q r mr v 0 y := by
  obtain ⟨κ,hQ,edge⟩ := start_counted_request ρ M n r v mr w Q hn hw hq hmaj
  have ready := start_ready ρ M (startInput n r v mr w) κ rfl hb hc hr hnp
    (by simpa only [hQ,startInput] using hj) (by simpa only [hQ,startInput] using hm) hbool
    (by simpa only [hQ] using (fun k => (hq k).1))
  exact ⟨_,edge,by simpa only [hQ,startInput] using ready⟩

/-- Complete concrete target implementation of atomic proposal insertion,
from idle through START and every scan node, with no assumed ready state. -/
theorem target_propose_walk (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (n r v mr w : Nat) (Q : Nat → Nat)
    (hb : ρ 8 = 0) (hc : ρ 9 = 0) (hr : r ≠ ρ 0) (hbool : BooleanSeven M)
    (hn : n < ρ 1) (hw : w < ρ 1)
    (hq : ∀ k, Q k ≤ 1 ∧ (1 ≤ Q k → k < ρ 1)) (hmaj : ρ 1 < 2 * quorumCount (ρ 1) Q)
    (hnp : ∀ z, M 3 (cpair r z) ≠ 1)
    (hj : ∀ k, 1 ≤ Q k → M 1 (cpair r k) = 1)
    (hm : mr = ρ 0 ∨ (1 ≤ Q w ∧ mr < r ∧ M 4 (cpair w (cpair mr v)) = 1))
    (rows : AllRows ⟨ρ 1,ρ 0,M⟩ Q r mr) :
    ∃ y, CSteps machine declarations (ρ,M) y ∧ Finished ⟨ρ 1,ρ 0,M⟩ r v y := by
  obtain ⟨x,edge,ready⟩ := encoded_start_step ρ M n r v mr w Q hb hc hr hbool hn hw hq hmaj hnp hj hm
  have pos : 0 < (ScanStore.mk (ρ 1) (ρ 0) M).size := by change 0 < ρ 1; omega
  obtain ⟨y,path,done⟩ := finish_concrete_scan ⟨ρ 1,ρ 0,M⟩ Q r mr v
    (fun mp hmp key => hbool mp (by omega) key) (fun k => (hq k).1) rows pos ready
  exact ⟨y,(Steps.next (.refl _) edge).trans path,done⟩

#print axioms encoded_start_step
#print axioms target_propose_walk
#print axioms start_actual_flags
#print axioms start_register_effect
#print axioms start_quorum_effect
#print axioms start_ready
end Bapa.PaxosEprTarget
