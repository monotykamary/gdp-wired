import PaxosEprAtomicDefs
namespace Bapa.PaxosEprAtomicSource
open Kern

private theorem and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all
private theorem and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp_all

theorem size_view (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    (sView machine ρ M ι κ).1 sizeId = ρ sizeId := by
  simp [sView, machine, sizeId, decideFlags, applyS, flagSub, assoc, lookup, decideQ, withInputs]

/-- Positive size is derived from the unchanged source request assumption,
not added as a precondition to its theorem. -/
theorem admitted_size_positive (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (ha : evalC (sView machine ρ M ι κ).1 (sView machine ρ M ι κ).2 machine.f.m.assume = true) :
    0 < ρ sizeId := by
  have hn : (sView machine ρ M ι κ).1 5 < (sView machine ρ M ι κ).1 sizeId := by
    exact of_decide_eq_true (and_left (and_right ha))
  have hv : 0 < (sView machine ρ M ι κ).1 sizeId := Nat.lt_of_le_of_lt (Nat.zero_le _) hn
  simpa only [size_view] using hv

/-- At zero nodes the source has no admitted transitions, including Propose. -/
theorem zero_size_no_request (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (hz : ρ sizeId = 0) :
    ¬ evalC (sView machine ρ M ι κ).1 (sView machine ρ M ι κ).2 machine.f.m.assume = true := by
  intro ha
  have hp := admitted_size_positive ρ M ι κ ha
  omega

theorem size_next (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    (sNext machine ρ M ι κ).1 sizeId = ρ sizeId := by
  change (sView machine ρ M ι κ).1 sizeId = ρ sizeId
  exact size_view ρ M ι κ

theorem zero_size_initial_maps {ds : List CDecl} {ρ M}
    (hr : CReach machine ds ρ M) (hz : ρ sizeId = 0) : StartMaps machine.f.m M := by
  induction hr with
  | start ρ M hm _ _ _ => exact hm
  | step ρ M ι κ _ _ ha _ =>
    have hp := admitted_size_positive ρ M ι κ ha
    rw [size_next] at hz
    omega

/-- Complete public-law coverage for every zero-node source run. -/
theorem zero_size_public_safety {ρ M} (hr : CReach machine declarations ρ M) (hz : ρ sizeId = 0) :
    safety.Holds ρ (withCnt declarations ρ M) := by
  have hm := zero_size_initial_maps hr hz
  have hd : ∀ key, M 5 key = 0 := hm (5,0) (by decide +kernel)
  simp [SEntry.Holds, safety, holdsOver, MLaw.Holds, evalC, evalE, withCnt, declarations, lookup, upd, hd]

#print axioms size_next
#print axioms zero_size_initial_maps
#print axioms zero_size_public_safety
#print axioms size_view
#print axioms admitted_size_positive
#print axioms zero_size_no_request
end Bapa.PaxosEprAtomicSource
