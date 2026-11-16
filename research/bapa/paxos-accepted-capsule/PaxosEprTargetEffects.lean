import PaxosEprTargetScan
namespace Bapa.PaxosEprTarget
open Kern

def BooleanSeven (N : Nat → Nat → Nat) : Prop := ∀ mp, mp < 7 → ∀ key, N mp key ≤ 1

private theorem bool_value {n : Nat} (h : n ≤ 1) : (if n = 1 then 1 else 0) = n := by
  by_cases hn : n = 1
  · simp [hn]
  · have hz : n = 0 := by omega
    simp [hz]

private theorem bool_value_decided {n : Nat} (h : n ≤ 1) :
    (if decide (n = 1) = true then 1 else 0) = n := by
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl <;> rfl

private theorem key_reconstruct (key : Nat) : cpair (pickP 0 key) (pickP 1 key) = key := by
  simp [pickP, cpair_cun]

/-- Exact public map effect of a successful scan: only its final step inserts
Proposal(pr,pv). Every interior step leaves all six public maps unchanged. -/
theorem scan_public_effect (V : Nat → Nat) (N : Nat → Nat → Nat) (hn : BooleanSeven N)
    (h73 : V 73 = 0) (h74 : V 74 = 0) (h79 : V 79 = 0) (h80 : V 80 = 0) :
    ∀ mp, mp < 6 → ∀ key, everyMaps machine V N mp key =
      if mp = 3 ∧ V 78 = 1 ∧ key = cpair (V 10) (V 12) then 1 else N mp key := by
  have hb : ∀ mp, mp < 7 → ∀ key, (if N mp key = 1 then 1 else 0) = N mp key :=
    fun mp hm key => bool_value (hn mp hm key)
  have hbd : ∀ mp, mp < 7 → ∀ key, (if decide (N mp key = 1) = true then 1 else 0) = N mp key :=
    fun mp hm key => bool_value_decided (hn mp hm key)
  intro mp hm key
  have cases : mp=0 ∨ mp=1 ∨ mp=2 ∨ mp=3 ∨ mp=4 ∨ mp=5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · by_cases hk : key = V 4 <;>
      simp [everyMaps, machine, lookup, writeMaps, evalE, evalC, h73, hk, hb, hbd] <;> exact hbd _ (by decide) _
  · by_cases hk : key = cpair (V 4) (V 3) <;>
      simp [everyMaps, machine, lookup, writeMaps, evalE, evalC, h74, hk, hb, hbd] <;> exact hbd _ (by decide) _
  · simp [everyMaps, machine, lookup, evalE, evalC, upd, h74, key_reconstruct, hb]
  · by_cases hk : key = cpair (V 10) (V 12) <;> by_cases hf : V 78 = 1 <;>
      simp [everyMaps, machine, lookup, writeMaps, evalE, evalC, hf, hk, hb, hbd] <;> exact hbd _ (by decide) _
  · by_cases hk : key = cpair (V 3) (cpair (V 4) (V 5)) <;>
      simp [everyMaps, machine, lookup, writeMaps, evalE, evalC, h79, hk, hb, hbd] <;> exact hbd _ (by decide) _
  · by_cases hk : key = cpair (V 4) (V 5) <;>
      simp [everyMaps, machine, lookup, writeMaps, evalE, evalC, h80, hk, hb, hbd] <;> exact hbd _ (by decide) _

theorem scan_quorum_effect (V : Nat → Nat) (N : Nat → Nat → Nat) (hn : BooleanSeven N)
    (h75 : V 75 = 0) (h77 : V 77 = 0) (key : Nat) :
    everyMaps machine V N 6 key = if V 78 = 1 then 0 else N 6 key := by
  have hb := bool_value (hn 6 (by decide) key)
  by_cases hf : V 78 = 1 <;>
    simp [everyMaps, machine, lookup, evalE, evalC, upd, h75, h77, hf, hb]

theorem scan_register_effect (V : Nat → Nat) (N : Nat → Nat → Nat)
    (h75 : V 75 = 0) (h76 : V 76 = 1) (h77 : V 77 = 0) :
    let W := applyS machine.f.m.step V N
    W 0 = V 0 ∧ W 1 = V 1 ∧
    W 8 = (if V 78 = 1 then 0 else V 8) ∧
    W 9 = (if V 78 = 1 then 0 else V 9 + 1) ∧
    W 10 = (if V 78 = 1 then 0 else V 10) ∧
    W 11 = (if V 78 = 1 then 0 else V 11) ∧
    W 12 = (if V 78 = 1 then 0 else V 12) := by
  by_cases hf : V 78 = 1 <;>
    simp [machine, applyS, assoc, lookup, evalE, evalC, h75, h76, h77, hf]

#print axioms scan_public_effect
#print axioms scan_quorum_effect
#print axioms scan_register_effect
end Bapa.PaxosEprTarget
