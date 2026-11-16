import PaxosEprSourceInitial
namespace Bapa.PaxosEprTarget
open Kern

def positiveMissing (size : Nat) (Q V : Nat → Nat) : Nat :=
 sumBelow (fun k => if (decide (1 ≤ Q k) && !decide (1 ≤ V k)) = true then 1 else 0) size

def unitMissing (size : Nat) (Q V : Nat → Nat) : Nat :=
 sumBelow (fun k => if (decide (1 ≤ Q k) && !decide (V k = 1)) = true then 1 else 0) size

theorem missing_agree (size : Nat) (Q V : Nat → Nat) (hb : ∀ k, V k ≤ 1) :
 positiveMissing size Q V = unitMissing size Q V := by
 apply congrArg (fun f => sumBelow f size)
 funext k
 have cases : V k = 0 ∨ V k = 1 := by have := hb k; omega
 rcases cases with h | h <;> simp [h]

theorem source_missing_count (ρ : Nat → Nat) (M : Nat → Nat → Nat)
 (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (hg : GHolds PaxosEprAtomicSource.declarations
  (withInputs PaxosEprAtomicSource.machine.f.m.inputs ρ ι) (withCarried PaxosEprAtomicSource.machine M κ)) :
 κ 8 0 = positiveMissing (ρ 0) (κ 6) (fun k => M 4 (cpair k (cpair (ι 6) (ι 7)))) := by
 let d : CDecl := ⟨8,10,35,36,.var 0,.ite (.and (.le (.const 1) (.get 6 (.var 36))) (.not (.le (.const 1) (.get 4 (.tup (.var 36) (.tup (.var 6) (.var 7))))))) (.const 1) (.const 0),35,0⟩
 have hd : d ∈ PaxosEprAtomicSource.declarations := by simp [d,PaxosEprAtomicSource.declarations]
 have h := hg d hd 0
 simpa [d,cntOf,atJ,evalE,evalC,upd,withInputs,withCarried,PaxosEprAtomicSource.machine,positiveMissing] using h

theorem target_missing_count (ρ : Nat → Nat) (M : Nat → Nat → Nat)
 (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (hg : GHolds declarations (withInputs machine.f.m.inputs ρ ι) (withCarried machine M κ)) :
 κ 9 0 = unitMissing (ρ 1) (κ 7) (fun k => M 4 (cpair k (cpair (ι 4) (ι 5)))) := by
 let d : CDecl := ⟨9,14,91,92,.var 1,.ite (.and (.le (.const 1) (.get 7 (.var 92))) (.not (.eq (.get 4 (.tup (.var 92) (.tup (.var 4) (.var 5)))) (.const 1)))) (.const 1) (.const 0),91,0⟩
 have hd : d ∈ declarations := by simp [d,declarations]
 have h := hg d hd 0
 simpa [d,cntOf,atJ,evalE,evalC,upd,withInputs,withCarried,machine,unitMissing] using h

/-- Realize every target count while preserving both the source quorum's
cardinality and its missing-vote count. The latter drives Decide. -/
theorem realize_source_request (ρs ρt : Nat → Nat) (Ms Mt : Nat → Nat → Nat)
 (ιs ιt : Nat → Nat) (κs : Nat → Nat → Nat)
 (size : ρt 1 = ρs 0) (round : ιt 4 = ιs 6) (value : ιt 5 = ιs 7)
 (votes : Mt 4 = Ms 4) (hb : ∀ key, Ms 4 key ≤ 1)
 (hg : GHolds PaxosEprAtomicSource.declarations
  (withInputs PaxosEprAtomicSource.machine.f.m.inputs ρs ιs) (withCarried PaxosEprAtomicSource.machine Ms κs)) :
 ∃ κt, GHolds declarations (withInputs machine.f.m.inputs ρt ιt) (withCarried machine Mt κt) ∧
  κt 7 = κs 6 ∧ κt 8 0 = κs 7 0 ∧ κt 9 0 = κs 8 0 := by
 obtain ⟨κt,hQ,hG,hC⟩ := source_to_target_quorum ρs ρt Ms Mt ιs ιt κs size hg
 refine ⟨κt,hG,hQ,hC,?_⟩
 calc
  κt 9 0 = unitMissing (ρt 1) (κt 7) (fun k => Mt 4 (cpair k (cpair (ιt 4) (ιt 5)))) := target_missing_count ρt Mt ιt κt hG
  _ = unitMissing (ρs 0) (κs 6) (fun k => Ms 4 (cpair k (cpair (ιs 6) (ιs 7)))) := by rw [size,hQ,round,value,votes]
  _ = positiveMissing (ρs 0) (κs 6) (fun k => Ms 4 (cpair k (cpair (ιs 6) (ιs 7)))) := (missing_agree _ _ _ (fun k => hb _)).symm
  _ = κs 8 0 := (source_missing_count ρs Ms ιs κs hg).symm

#print axioms missing_agree
#print axioms source_missing_count
#print axioms target_missing_count
#print axioms realize_source_request
end Bapa.PaxosEprTarget
