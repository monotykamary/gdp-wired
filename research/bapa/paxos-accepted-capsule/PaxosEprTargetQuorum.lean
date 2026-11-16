import PaxosEprTargetCounts
import PaxosEprAtomicDefs
namespace Bapa.PaxosEprTarget
open Kern

def quorumCount (size : Nat) (Q : Nat → Nat) : Nat :=
  sumBelow (fun k => if decide (1 ≤ Q k) = true then 1 else 0) size

theorem target_members_count (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hg : GHolds declarations (withInputs machine.f.m.inputs ρ ι) (withCarried machine M κ)) :
    κ 8 0 = quorumCount (ρ 1) (κ 7) := by
  let d : CDecl := ⟨8,13,89,90,.var 1,.ite (.le (.const 1) (.get 7 (.var 90))) (.const 1) (.const 0),89,0⟩
  have hd : d ∈ declarations := by simp [d,declarations]
  have h := hg d hd 0
  simpa [d,cntOf,atJ,evalE,evalC,upd,withInputs,withCarried,machine,quorumCount] using h

theorem source_members_count (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hg : GHolds PaxosEprAtomicSource.declarations
      (withInputs PaxosEprAtomicSource.machine.f.m.inputs ρ ι)
      (withCarried PaxosEprAtomicSource.machine M κ)) :
    κ 7 0 = quorumCount (ρ 0) (κ 6) := by
  let d : CDecl := ⟨7,9,33,34,.var 0,.ite (.le (.const 1) (.get 6 (.var 34))) (.const 1) (.const 0),33,0⟩
  have hd : d ∈ PaxosEprAtomicSource.declarations := by simp [d,PaxosEprAtomicSource.declarations]
  have h := hg d hd 0
  simpa [d,cntOf,atJ,evalE,evalC,upd,withInputs,withCarried,PaxosEprAtomicSource.machine,quorumCount] using h

/-- Realize all target counts with an exact requested quorum, not just its
cardinality. The request therefore preserves row membership and majority. -/
theorem realize_quorum (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (Q : Nat → Nat) :
    ∃ κ, κ 7 = Q ∧
      GHolds declarations (withInputs machine.f.m.inputs ρ ι) (withCarried machine M κ) ∧
      κ 8 0 = quorumCount (ρ 1) Q := by
  let base : Nat → Nat → Nat := fun mp k => if mp = 7 then Q k else 0
  obtain ⟨κ,hoff,hg⟩ := realize_counts ρ M ι base
  have he := hoff 7 (by decide +kernel)
  have hq : κ 7 = Q := by simpa [withCarried,machine,base] using he
  have hc := target_members_count ρ M ι κ hg
  rw [hq] at hc
  exact ⟨κ,hq,hg,hc⟩

theorem source_to_target_quorum (ρs ρt : Nat → Nat) (Ms Mt : Nat → Nat → Nat)
    (ιs ιt : Nat → Nat) (κs : Nat → Nat → Nat) (size : ρt 1 = ρs 0)
    (hg : GHolds PaxosEprAtomicSource.declarations
      (withInputs PaxosEprAtomicSource.machine.f.m.inputs ρs ιs)
      (withCarried PaxosEprAtomicSource.machine Ms κs)) :
    ∃ κt, κt 7 = κs 6 ∧
      GHolds declarations (withInputs machine.f.m.inputs ρt ιt) (withCarried machine Mt κt) ∧
      κt 8 0 = κs 7 0 := by
  obtain ⟨κt,hq,ht,hc⟩ := realize_quorum ρt Mt ιt (κs 6)
  have hs := source_members_count ρs Ms ιs κs hg
  rw [size] at hc
  exact ⟨κt,hq,ht,hc.trans hs.symm⟩

#print axioms target_members_count
#print axioms source_members_count
#print axioms realize_quorum
#print axioms source_to_target_quorum
end Bapa.PaxosEprTarget
