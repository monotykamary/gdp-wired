import PaxosEprOrdinaryCounts
namespace Bapa.PaxosEprSourceScan
open Kern

def ordinaryInput (ι : Nat → Nat) : Nat → Nat := fun i => match i with
 | 2 => if ι 4 < 2 then ι 4 else ι 4 + 1
 | 3 => ι 5 | 4 => ι 6 | 5 => ι 7 | 6 => ι 8 | 7 => ι 9 | _ => 0

def Ordinary (ι : Nat → Nat) : Prop := ι 4 = 0 ∨ ι 4 = 1 ∨ ι 4 = 3 ∨ ι 4 = 4

theorem ordinary_flags (ρ : Nat → Nat) (M : Nat → Nat → Nat)
 (ι : Nat → Nat) (κ κt : Nat → Nat → Nat) {x : Bapa.FiniteSimulation.KState}
 (hx : Idle (atomicStore ρ M) x) (hop : Ordinary ι)
 (hb : PaxosEprAtomicSource.BooleanMaps M) (hc : κt 9 0 = κ 8 0) :
 let S := (sView PaxosEprAtomicSource.machine ρ M ι κ).1
 let T := (sView PaxosEprTarget.machine x.1 x.2 (ordinaryInput ι) κt).1
 T 73 = S 14 ∧ T 74 = S 15 ∧ T 75 = 0 ∧ T 76 = 0 ∧ T 77 = 0 ∧ T 78 = 0 ∧
 T 79 = S 17 ∧ T 80 = S 18 ∧ S 16 = 0 := by
 have none : x.1 0 = ρ 3 := hx.none
 have busy : x.1 8 = 0 := hx.busy
 have m0 : x.2 0 = M 0 := funext (fun key => hx.publicMaps 0 (by decide) key)
 have m2 : x.2 2 = M 2 := funext (fun key => hx.publicMaps 2 (by decide) key)
 have m3 : x.2 3 = M 3 := funext (fun key => hx.publicMaps 3 (by decide) key)
 have p2 (key : Nat) : 1 ≤ M 2 key ↔ M 2 key = 1 := by have := hb 2 (by decide) key; omega
 have p3 (key : Nat) : 1 ≤ M 3 key ↔ M 3 key = 1 := by have := hb 3 (by decide) key; omega
 rcases hop with hop | hop | hop | hop <;>
  simp [sView,PaxosEprAtomicSource.machine,PaxosEprTarget.machine,decideFlags,applyS,
    flagSub,assoc,lookup,decideQ,withInputs,withCarried,evalE,evalC,ordinaryInput,hop,
    none,busy,m0,m2,m3,p2,p3,hc,Bool.and_assoc]

#print axioms ordinary_flags
end Bapa.PaxosEprSourceScan
