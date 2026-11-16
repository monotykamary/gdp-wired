import PaxosEprOrdinaryAdmission
namespace Bapa.PaxosEprSourceScan
open Kern

theorem ordinary_public_agree (S T : Nat → Nat) (A B : Nat → Nat → Nat)
 (hb : PaxosEprAtomicSource.BooleanMaps A) (maps : ∀ mp, mp < 6 → B mp = A mp)
 (hn : T 3 = S 5) (hr : T 4 = S 6) (hv : T 5 = S 7)
 (hs : T 73 = S 14) (hj : T 74 = S 15) (hvo : T 79 = S 17) (hd : T 80 = S 18)
 (hps : S 16 = 0) (hpt : T 78 = 0) :
 ∀ mp, mp < 6 → ∀ key, everyMaps PaxosEprTarget.machine T B mp key =
  everyMaps PaxosEprAtomicSource.machine S A mp key := by
 have m0 := maps 0 (by decide)
 have m1 := maps 1 (by decide)
 have m2 := maps 2 (by decide)
 have m3 := maps 3 (by decide)
 have m4 := maps 4 (by decide)
 have m5 := maps 5 (by decide)
 have bit (mp) (hm : mp < 6) (key) : (if A mp key = 1 then 1 else 0) = A mp key := by
  have h := hb mp hm key
  have cases : A mp key = 0 ∨ A mp key = 1 := by omega
  rcases cases with h | h <;> simp [h]
 have bitD (mp) (hm : mp < 6) (key) : (if decide (A mp key = 1) = true then 1 else 0) = A mp key := by
  have h := hb mp hm key
  have cases : A mp key = 0 ∨ A mp key = 1 := by omega
  rcases cases with h | h <;> simp [h]
 have positive2 (key : Nat) : 1 ≤ A 2 key ↔ A 2 key = 1 := by have := hb 2 (by decide) key; omega
 have kr (key : Nat) : cpair (pickP 0 key) (pickP 1 key) = key := by simp [pickP]
 intro mp hmp key
 have cases : mp=0 ∨ mp=1 ∨ mp=2 ∨ mp=3 ∨ mp=4 ∨ mp=5 := by omega
 rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
 · by_cases hk : key = S 6 <;> by_cases hf : S 14 = 1 <;> by_cases ho : A 0 (S 6) = 1 <;>
    simp [everyMaps,PaxosEprTarget.machine,PaxosEprAtomicSource.machine,lookup,writeMaps,
      evalE,evalC,hr,hs,m0,hk,hf,ho]
 · by_cases hk : key = cpair (S 6) (S 5) <;> by_cases hf : S 15 = 1 <;>
    simp [everyMaps,PaxosEprTarget.machine,PaxosEprAtomicSource.machine,lookup,writeMaps,
      evalE,evalC,hr,hn,hj,m1,hk,hf,bit,bitD] <;> exact bitD _ (by decide) _
 · have h := hb 2 (by decide) key
   have cases : A 2 key = 0 ∨ A 2 key = 1 := by omega
   rcases cases with h | h <;> by_cases hf : S 15 = 1 <;>
    by_cases hn' : pickP 0 key = S 5 <;> by_cases hr' : pickP 1 key < S 6 <;>
    simp [everyMaps,PaxosEprTarget.machine,PaxosEprAtomicSource.machine,lookup,
      evalE,evalC,upd,hr,hn,hj,m2,kr,h,hf,hn',hr',positive2]
 · by_cases hkt : key = cpair (T 10) (T 12) <;> by_cases hks : key = cpair (S 6) (S 7) <;>
    simp [everyMaps,PaxosEprTarget.machine,PaxosEprAtomicSource.machine,lookup,writeMaps,
      evalE,evalC,hps,hpt,m3,hkt,hks,bit,bitD] <;> intro he <;> simp only [he]
 · by_cases hk : key = cpair (S 5) (cpair (S 6) (S 7)) <;> by_cases hf : S 17 = 1 <;>
    simp [everyMaps,PaxosEprTarget.machine,PaxosEprAtomicSource.machine,lookup,writeMaps,
      evalE,evalC,hn,hr,hv,hvo,m4,hk,hf,bit,bitD] <;> exact bitD _ (by decide) _
 · by_cases hk : key = cpair (S 6) (S 7) <;> by_cases hf : S 18 = 1 <;>
    simp [everyMaps,PaxosEprTarget.machine,PaxosEprAtomicSource.machine,lookup,writeMaps,
      evalE,evalC,hr,hv,hd,m5,hk,hf,bit,bitD] <;> exact bitD _ (by decide) _

theorem ordinary_register_effect (T : Nat → Nat) (B : Nat → Nat → Nat)
 (h75 : T 75 = 0) (h76 : T 76 = 0) (h77 : T 77 = 0) (h78 : T 78 = 0) :
 let W := applyS PaxosEprTarget.machine.f.m.step T B
 W 0 = T 0 ∧ W 1 = T 1 ∧ W 8 = T 8 ∧ W 9 = T 9 ∧
 W 10 = T 10 ∧ W 11 = T 11 ∧ W 12 = T 12 := by
 simp [PaxosEprTarget.machine,applyS,assoc,lookup,evalE,evalC,h75,h76,h77,h78]

#print axioms ordinary_public_agree
#print axioms ordinary_register_effect
end Bapa.PaxosEprSourceScan
