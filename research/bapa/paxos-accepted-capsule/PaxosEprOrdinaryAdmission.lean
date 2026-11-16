import PaxosEprOrdinaryFlags
namespace Bapa.PaxosEprSourceScan
open Kern

private theorem and_parts {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
 cases a <;> cases b <;> simp_all

theorem source_request_bounds (ρ : Nat → Nat) (M : Nat → Nat → Nat)
 (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (ha : evalC (sView PaxosEprAtomicSource.machine ρ M ι κ).1 (sView PaxosEprAtomicSource.machine ρ M ι κ).2 PaxosEprAtomicSource.machine.f.m.assume = true) :
 ι 5 < ρ 0 ∧ ι 9 < ρ 0 := by
 have hn : decide ((sView PaxosEprAtomicSource.machine ρ M ι κ).1 5 < (sView PaxosEprAtomicSource.machine ρ M ι κ).1 0) = true :=
  (and_parts (and_parts ha).2).1
 have hw : decide ((sView PaxosEprAtomicSource.machine ρ M ι κ).1 9 < (sView PaxosEprAtomicSource.machine ρ M ι κ).1 0) = true :=
  (and_parts (and_parts (and_parts ha).2).2).1
 constructor
 · simpa only [PaxosEprAtomicSource.Propose.v_input ρ M ι κ 5 (by decide),PaxosEprAtomicSource.Propose.v_static ρ M ι κ 0 (by decide)] using of_decide_eq_true hn
 · simpa only [PaxosEprAtomicSource.Propose.v_input ρ M ι κ 9 (by decide),PaxosEprAtomicSource.Propose.v_static ρ M ι κ 0 (by decide)] using of_decide_eq_true hw

theorem decision_view_requirements (D : Nat → Nat) (N : Nat → Nat → Nat)
 (hop : D 4 = 4) (h : evalC D N PaxosEprAtomicSource.machine.f.m.assume = true) :
 D 19 = 1 ∧ D 0 < 2 * N 7 0 := by
 simp [PaxosEprAtomicSource.machine,evalC,evalE,hop] at h
 obtain ⟨_,_,_,_,_,hq,hm⟩ := h
 refine ⟨of_decide_eq_true hq,?_⟩
 first | exact of_decide_eq_true hm | exact hm

theorem ordinary_view_admitted (D : Nat → Nat) (N : Nat → Nat → Nat)
 (hop : D 2 = 0 ∨ D 2 = 1 ∨ D 2 = 4 ∨ D 2 = 5)
 (hn : D 3 < D 1) (hw : D 7 < D 1)
 (hreq : D 2 = 5 → D 81 = 1 ∧ D 1 < 2 * N 8 0) :
 evalC D N PaxosEprTarget.machine.f.m.assume = true := by
 rcases hop with h | h | h | h
 · simp [PaxosEprTarget.machine,evalC,evalE,h,hn,hw]
 · simp [PaxosEprTarget.machine,evalC,evalE,h,hn,hw]
 · simp [PaxosEprTarget.machine,evalC,evalE,h,hn,hw]
 · obtain ⟨hq,hm⟩ := hreq h
   simp [PaxosEprTarget.machine,evalC,evalE,h,hn,hw,hq,hm]

theorem ordinary_admitted (ρ : Nat → Nat) (M : Nat → Nat → Nat)
 (ι : Nat → Nat) (κ κt : Nat → Nat → Nat) {x : Bapa.FiniteSimulation.KState}
 (hx : Idle (atomicStore ρ M) x) (hop : Ordinary ι)
 (hQ : κt 7 = κ 6) (hMembers : κt 8 0 = κ 7 0)
 (ha : evalC (sView PaxosEprAtomicSource.machine ρ M ι κ).1 (sView PaxosEprAtomicSource.machine ρ M ι κ).2 PaxosEprAtomicSource.machine.f.m.assume = true) :
 evalC (sView PaxosEprTarget.machine x.1 x.2 (ordinaryInput ι) κt).1
  (sView PaxosEprTarget.machine x.1 x.2 (ordinaryInput ι) κt).2 PaxosEprTarget.machine.f.m.assume = true := by
 let D := (sView PaxosEprTarget.machine x.1 x.2 (ordinaryInput ι) κt).1
 let N := (sView PaxosEprTarget.machine x.1 x.2 (ordinaryInput ι) κt).2
 have t2 : D 2 = ordinaryInput ι 2 := PaxosEprTarget.view_input _ _ _ _ 2 (by decide)
 have top : D 2 = 0 ∨ D 2 = 1 ∨ D 2 = 4 ∨ D 2 = 5 := by
  rw [t2]
  rcases hop with h | h | h | h <;> simp [ordinaryInput,h]
 have bounds := source_request_bounds ρ M ι κ ha
 apply ordinary_view_admitted D N top
 · simpa only [D,PaxosEprTarget.view_input _ _ _ _ 3 (by decide),PaxosEprTarget.view_fixed _ _ _ _ 1 (by decide),ordinaryInput,hx.size,atomicStore] using bounds.1
 · simpa only [D,PaxosEprTarget.view_input _ _ _ _ 7 (by decide),PaxosEprTarget.view_fixed _ _ _ _ 1 (by decide),ordinaryInput,hx.size,atomicStore] using bounds.2
 · intro ht
   have is4 : ι 4 = 4 := by
    rcases hop with h | h | h | h
    · simp [t2,ordinaryInput,h] at ht
    · simp [t2,ordinaryInput,h] at ht
    · simp [t2,ordinaryInput,h] at ht
    · exact h
   have op := (PaxosEprAtomicSource.Propose.v_input ρ M ι κ 4 (by decide)).trans is4
   obtain ⟨qflag,major⟩ := decision_view_requirements _ _ op ha
   have valid := PaxosEprAtomicSource.quorumValid_from_flag ρ M ι κ qflag
   have validT : ∀ k, κt 7 k ≤ 1 ∧ (1 ≤ κt 7 k → k < x.1 1) := by
    intro k
    simpa only [hQ,hx.size,atomicStore] using valid k
   refine ⟨PaxosEprTarget.valid_quorum_flag _ _ _ _ validT,?_⟩
   have n7 : (sView PaxosEprAtomicSource.machine ρ M ι κ).2 7 0 = κ 7 0 := rfl
   have majorS : ρ 0 < 2 * κ 7 0 := by
    simpa only [PaxosEprAtomicSource.Propose.v_static ρ M ι κ 0 (by decide),n7] using major
   have n8 : N 8 0 = κt 8 0 := rfl
   simpa only [D,PaxosEprTarget.view_fixed _ _ _ _ 1 (by decide),n8,hMembers,hx.size,atomicStore] using majorS

#print axioms source_request_bounds
#print axioms decision_view_requirements
#print axioms ordinary_view_admitted
#print axioms ordinary_admitted
end Bapa.PaxosEprSourceScan
