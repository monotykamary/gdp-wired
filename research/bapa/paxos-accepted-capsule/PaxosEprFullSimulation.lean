import PaxosEprOrdinaryExecution
import PaxosEprSourceStutter
namespace Bapa.PaxosEprSourceScan
open Kern Bapa.FiniteSimulation

private theorem and_left {a b : Bool} (h : (a && b) = true) : a = true := by
 cases a <;> cases b <;> simp_all

def SimulationRelation (x y : KState) : Prop := Idle (atomicStore x.1 x.2) y

/-- Every original size, including zero; positive size is derived only when a
source request is actually admitted. Propose uses finite counted scanning,
ordinary requests use one counted edge, disabled Propose uses zero edges. -/
theorem full_simulation : CSimulation PaxosEprAtomicSource.machine PaxosEprAtomicSource.declarations
 PaxosEprTarget.machine PaxosEprTarget.declarations SimulationRelation := by
 refine ⟨source_initial_matches,?_⟩
 intro x x' y reach _ rel edge
 obtain ⟨ι,κ,hg,ha,rfl⟩ := edge
 have hr := creach_out reach
 by_cases hop : ι 4 = 2
 · exact matched_propose hr ι κ hop hg ha rel
 · have hb : decide ((sView PaxosEprAtomicSource.machine x.1 x.2 ι κ).1 4 < 5) = true := and_left ha
   have hb' : ι 4 < 5 := by
    simpa only [PaxosEprAtomicSource.Propose.v_input _ _ _ _ 4 (by decide)] using of_decide_eq_true hb
   have ho : Ordinary ι := by unfold Ordinary; omega
   obtain ⟨y',he,hy'⟩ := matched_ordinary hr ι κ ho hg ha rel
   exact ⟨y',.next (.refl _) he,hy'⟩

def Agreement (M : Nat → Nat → Nat) : Prop :=
 ∀ r r' v v', 1 ≤ M 5 (cpair r v) → 1 ≤ M 5 (cpair r' v') → v = v'

theorem idle_agreement {ρ M y} (rel : Idle (atomicStore ρ M) y) (h : Agreement y.2) : Agreement M := by
 intro r r' v v' h1 h2
 apply h r r' v v'
 · rw [rel.publicMaps 5 (by decide)]; exact h1
 · rw [rel.publicMaps 5 (by decide)]; exact h2

theorem agreement_source_safety (ρ : Nat → Nat) (M : Nat → Nat → Nat) (h : Agreement M) :
 PaxosEprAtomicSource.safety.Holds ρ (withCnt PaxosEprAtomicSource.declarations ρ M) := by
 intro v r' v' r
 have agree := h r r' v v'
 have disj : M 5 (cpair r v) = 0 ∨ M 5 (cpair r' v') = 0 ∨ v = v' := by
  by_cases h1 : M 5 (cpair r v) = 0
  · exact Or.inl h1
  · by_cases h2 : M 5 (cpair r' v') = 0
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (agree (by omega) (by omega)))
 simp [PaxosEprAtomicSource.safety,evalC,evalE,upd,withCnt,PaxosEprAtomicSource.declarations,lookup]
 omega

/-- Conditional ONLY on a proved target invariant. This is not an assertion
that the pending target certificate family has passed its counted gate. -/
theorem source_safety_from_target
 (ht : ∀ ρ M, CReach PaxosEprTarget.machine PaxosEprTarget.declarations ρ M → Agreement M)
 {ρ M} (hr : CReach PaxosEprAtomicSource.machine PaxosEprAtomicSource.declarations ρ M) :
 PaxosEprAtomicSource.safety.Holds ρ (withCnt PaxosEprAtomicSource.declarations ρ M) := by
 obtain ⟨y,hy,rel⟩ := cprojected_reach full_simulation hr
 exact agreement_source_safety ρ M (idle_agreement rel (ht y.1 y.2 hy))

/-- Concrete law control: two different decided values fail the ORIGINAL
source law. This state is not asserted reachable. -/
theorem source_safety_negative_control :
 ¬ PaxosEprAtomicSource.safety.Holds (fun i => if i=2 then 2 else 1)
  (withCnt PaxosEprAtomicSource.declarations (fun i => if i=2 then 2 else 1)
    (fun mp _ => if mp=5 then 1 else 0)) := by
 intro h
 have bad := h 0 0 1 0
 simp [PaxosEprAtomicSource.safety,evalC,evalE,upd,withCnt,PaxosEprAtomicSource.declarations,lookup] at bad

#print axioms full_simulation
#print axioms agreement_source_safety
#print axioms source_safety_from_target
#print axioms source_safety_negative_control
end Bapa.PaxosEprSourceScan
