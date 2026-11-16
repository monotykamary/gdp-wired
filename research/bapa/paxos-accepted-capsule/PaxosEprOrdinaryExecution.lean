import PaxosEprOrdinaryEffects
namespace Bapa.PaxosEprSourceScan
open Kern Bapa.FiniteSimulation

theorem ordinary_execution (ρ : Nat → Nat) (M : Nat → Nat → Nat)
 (ι : Nat → Nat) (κ κt : Nat → Nat → Nat) {x : KState}
 (hx : Idle (atomicStore ρ M) x) (hop : Ordinary ι)
 (hb : PaxosEprAtomicSource.BooleanMaps M) (hc : κt 9 0 = κ 8 0) :
 Idle (atomicStore (sNext PaxosEprAtomicSource.machine ρ M ι κ).1
  (sNext PaxosEprAtomicSource.machine ρ M ι κ).2)
  (sNext PaxosEprTarget.machine x.1 x.2 (ordinaryInput ι) κt) := by
 let S := (sView PaxosEprAtomicSource.machine ρ M ι κ).1
 let A := withCarried PaxosEprAtomicSource.machine M κ
 let T := (sView PaxosEprTarget.machine x.1 x.2 (ordinaryInput ι) κt).1
 let B := withCarried PaxosEprTarget.machine x.2 κt
 have alow (mp : Nat) (hm : mp < 6) : A mp = M mp := by
  have cases : mp=0 ∨ mp=1 ∨ mp=2 ∨ mp=3 ∨ mp=4 ∨ mp=5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
 have blow (mp : Nat) (hm : mp < 7) : B mp = x.2 mp := PaxosEprTarget.carried_low _ _ mp hm
 have sameMaps (mp : Nat) (hm : mp < 6) : B mp = A mp := by
  rw [blow mp (by omega),alow mp hm]
  exact funext (fun key => hx.publicMaps mp hm key)
 have ab : PaxosEprAtomicSource.BooleanMaps A := by
  intro mp hm key
  rw [alow mp hm]
  exact hb mp hm key
 have bb : PaxosEprTarget.BooleanSeven B := by
  intro mp hm key
  by_cases he : mp = 6
  · subst mp
    rw [blow 6 (by decide),hx.quorum]
    omega
  · rw [sameMaps mp (by omega)]
    exact ab mp (by omega) key
 have vf (i : Nat) (hi : PaxosEprTarget.FixedRegister i) : T i = x.1 i := PaxosEprTarget.view_fixed _ _ _ _ i hi
 have tn : T 3 = S 5 := by
  simp only [T,S,PaxosEprTarget.view_input _ _ _ _ 3 (by decide),PaxosEprAtomicSource.Propose.v_input _ _ _ _ 5 (by decide),ordinaryInput]
 have tr : T 4 = S 6 := by
  simp only [T,S,PaxosEprTarget.view_input _ _ _ _ 4 (by decide),PaxosEprAtomicSource.Propose.v_input _ _ _ _ 6 (by decide),ordinaryInput]
 have tv : T 5 = S 7 := by
  simp only [T,S,PaxosEprTarget.view_input _ _ _ _ 5 (by decide),PaxosEprAtomicSource.Propose.v_input _ _ _ _ 7 (by decide),ordinaryInput]
 obtain ⟨hs,hj,h75,h76,h77,h78,hvo,hd,hps⟩ := ordinary_flags ρ M ι κ κt hx hop hb hc
 have pub := ordinary_public_agree S T A B ab sameMaps tn tr tv hs hj hvo hd hps h78
 obtain ⟨r0,r1,r8,r9,r10,r11,r12⟩ := ordinary_register_effect T B h75 h76 h77 h78
 have ne := PaxosEprAtomicSource.Propose.static_next ρ M ι κ 3 (by decide)
 have se := PaxosEprAtomicSource.Propose.static_next ρ M ι κ 0 (by decide)
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · exact r0.trans ((vf 0 (by decide)).trans (hx.none.trans ne.symm))
 · exact r1.trans ((vf 1 (by decide)).trans (hx.size.trans se.symm))
 · exact r8.trans ((vf 8 (by decide)).trans hx.busy)
 · exact r9.trans ((vf 9 (by decide)).trans hx.count)
 · exact r10.trans ((vf 10 (by decide)).trans hx.round)
 · exact r11.trans ((vf 11 (by decide)).trans hx.maxRound)
 · exact r12.trans ((vf 12 (by decide)).trans hx.value)
 · intro mp hm key
   simpa only [sNext,sView,T,B,S,A,atomicStore] using pub mp hm key
 · intro key
   have h := PaxosEprTarget.scan_quorum_effect T B bb h75 h77 key
   have hz : T 78 = 0 := h78
   have hq : B 6 key = 0 := by rw [blow 6 (by decide)]; exact hx.quorum key
   simp only [hz,show ¬ (0:Nat)=1 from by decide,if_false,hq] at h
   exact h

theorem matched_ordinary {ρ : Nat → Nat} {M : Nat → Nat → Nat}
 (reach : CReach PaxosEprAtomicSource.machine PaxosEprAtomicSource.declarations ρ M)
 (ι : Nat → Nat) (κ : Nat → Nat → Nat) (hop : Ordinary ι)
 (hg : GHolds PaxosEprAtomicSource.declarations
   (withInputs PaxosEprAtomicSource.machine.f.m.inputs ρ ι) (withCarried PaxosEprAtomicSource.machine M κ))
 (ha : evalC (sView PaxosEprAtomicSource.machine ρ M ι κ).1 (sView PaxosEprAtomicSource.machine ρ M ι κ).2 PaxosEprAtomicSource.machine.f.m.assume = true)
 {x : KState} (hx : Idle (atomicStore ρ M) x) :
 ∃ y, CTransition PaxosEprTarget.machine PaxosEprTarget.declarations x y ∧
  Idle (atomicStore (sNext PaxosEprAtomicSource.machine ρ M ι κ).1 (sNext PaxosEprAtomicSource.machine ρ M ι κ).2) y := by
 have hb := PaxosEprAtomicSource.counted_reachable_boolean reach
 have votes : x.2 4 = M 4 := funext (fun key => hx.publicMaps 4 (by decide) key)
 obtain ⟨κt,hG,hQ,hC,hMiss⟩ := PaxosEprTarget.realize_source_request ρ x.1 M x.2 ι (ordinaryInput ι) κ
  hx.size rfl rfl votes (hb 4 (by decide)) hg
 have ht := ordinary_admitted ρ M ι κ κt hx hop hQ hC ha
 exact ⟨_,⟨ordinaryInput ι,κt,hG,ht,rfl⟩,ordinary_execution ρ M ι κ κt hx hop hb hMiss⟩

#print axioms ordinary_execution
#print axioms matched_ordinary
end Bapa.PaxosEprSourceScan
