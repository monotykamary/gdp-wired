import PaxosEprTargetEffects
namespace Bapa.PaxosEprTarget
open Kern

noncomputable def qView (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) :=
  decideQ machine (withInputs machine.f.m.inputs ρ ι) (withCarried machine M κ)

def FixedRegister (i : Nat) : Prop := i=0 ∨ i=1 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12
instance (i : Nat) : Decidable (FixedRegister i) := by unfold FixedRegister; infer_instance

theorem qView_fixed (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (i : Nat) (hi : FixedRegister i) :
    qView ρ M ι κ i = ρ i := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [qView, decideQ, machine, lookup, withInputs]

theorem view_fixed (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (i : Nat) (hi : FixedRegister i) :
    (sView machine ρ M ι κ).1 i = ρ i := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sView, decideFlags, applyS, flagSub, assoc, lookup, decideQ, machine, withInputs]

theorem view_q72 (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    (sView machine ρ M ι κ).1 72 = qView ρ M ι κ 72 := by
  simp [sView, qView, decideFlags, applyS, flagSub, assoc, lookup, machine]

theorem carried_low (M κ : Nat → Nat → Nat) (mp : Nat) (hm : mp < 7) :
    withCarried machine M κ mp = M mp := by
  have h : mp=0 ∨ mp=1 ∨ mp=2 ∨ mp=3 ∨ mp=4 ∨ mp=5 ∨ mp=6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem scan_actual_flags (ρ : Nat → Nat) (M : Nat → Nat → Nat) (κ : Nat → Nat → Nat)
    (hb : ρ 8 = 1)
    (hall : M 6 (ρ 9) = 1 → ∀ r v, M 4 (cpair (ρ 9) (cpair r v)) = 1 →
      r < ρ 10 → ρ 11 ≠ ρ 0 ∧ r ≤ ρ 11) :
    let V := (sView machine ρ M scanInput κ).1
    V 73 = 0 ∧ V 74 = 0 ∧ V 75 = 0 ∧ V 76 = 1 ∧ V 77 = 0 ∧
      V 78 = (if ρ 9 + 1 = ρ 1 then 1 else 0) ∧ V 79 = 0 ∧ V 80 = 0 := by
  have hop : qView ρ M scanInput κ 2 = 3 := by
    simp [qView, decideQ, machine, lookup, withInputs, scanInput]
  have hbusy : qView ρ M scanInput κ 8 = 1 := by
    rw [qView_fixed ρ M scanInput κ 8 (by decide)]
    exact hb
  have hrow : withCarried machine M κ 6 (qView ρ M scanInput κ 9) = 1 →
      qView ρ M scanInput κ 72 = 1 := by
    intro hq
    have hq' : M 6 (ρ 9) = 1 := by
      simpa only [qView_fixed ρ M scanInput κ 9 (by decide),
        carried_low M κ 6 (by decide)] using hq
    have hr := row_flag_of_all ρ M scanInput κ (hall hq')
    simpa only [view_q72] using hr
  have h := scan_plain_flags (qView ρ M scanInput κ) (withCarried machine M κ) hop hbusy hrow
  simp only [qView_fixed ρ M scanInput κ 9 (by decide),
    qView_fixed ρ M scanInput κ 1 (by decide)] at h
  simpa only [sView, qView] using h

#print axioms view_fixed
#print axioms scan_actual_flags
end Bapa.PaxosEprTarget
