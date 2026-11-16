import PaxosEprAtomicSupport
namespace Bapa.PaxosEprAtomicSource
open Kern

def BooleanMaps (M : Nat → Nat → Nat) : Prop := ∀ mp, mp < 6 → ∀ key, M mp key ≤ 1

private theorem physical_cases {mp : Nat} (h : mp < 6) :
    mp = 0 ∨ mp = 1 ∨ mp = 2 ∨ mp = 3 ∨ mp = 4 ∨ mp = 5 := by omega

theorem boolean_start {M} (hm : StartMaps machine.f.m M) : BooleanMaps M := by
  intro mp hmp key
  have mem : (mp,0) ∈ machine.f.m.maps0 := by
    rcases physical_cases hmp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have hz : M mp key = 0 := hm (mp,0) mem key
  omega

theorem boolean_carried {M} (hm : BooleanMaps M) (κ : Nat → Nat → Nat) :
    BooleanMaps (withCarried machine M κ) := by
  intro mp hmp key
  rcases physical_cases hmp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    change M _ key ≤ 1 <;> exact hm _ (by decide) key

private theorem bounded_ite {p : Prop} [Decidable p] {x y : Nat}
    (hx : x ≤ 1) (hy : y ≤ 1) : (if p then x else y) ≤ 1 := by
  by_cases h : p
  · simpa only [if_pos h] using hx
  · simpa only [if_neg h] using hy

theorem boolean_every (D : Nat → Nat) {N} (hn : BooleanMaps N) :
    BooleanMaps (everyMaps machine D N) := by
  intro mp hmp key
  rcases physical_cases hmp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [everyMaps, machine, lookup, writeMaps, evalE] <;> first
    | exact bounded_ite (by decide) (by decide)
    | exact bounded_ite (bounded_ite (by decide) (by decide)) (hn _ (by decide) _)
    | exact bounded_ite (bounded_ite (by decide) (hn _ (by decide) _)) (hn _ (by decide) _)

theorem boolean_step (ρ : Nat → Nat) {M} (hm : BooleanMaps M) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    BooleanMaps (sNext machine ρ M ι κ).2 := by
  exact boolean_every (sView machine ρ M ι κ).1 (boolean_carried hm κ)

theorem reachable_boolean {ρ M} (hr : SReach machine ρ M) : BooleanMaps M := by
  induction hr with
  | start _ M hm _ _ _ => exact boolean_start hm
  | step ρ M ι κ _ _ ih => exact boolean_step ρ ih ι κ

theorem counted_reachable_boolean {ds : List CDecl} {ρ M} (hr : CReach machine ds ρ M) :
    BooleanMaps M := reachable_boolean (creach_sreach hr)

theorem positive_iff_one {M} (hm : BooleanMaps M) (mp : Nat) (hmp : mp < 6) (key : Nat) :
    1 ≤ M mp key ↔ M mp key = 1 := by
  have h := hm mp hmp key
  omega

#print axioms reachable_boolean
#print axioms counted_reachable_boolean
#print axioms positive_iff_one
end Bapa.PaxosEprAtomicSource
