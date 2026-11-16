import PaxosEprTargetState
namespace Bapa.PaxosEprTarget
open Kern Bapa.FiniteSimulation

def ScanEffect (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (σ : Nat → Nat) (N : Nat → Nat → Nat) : Prop :=
  σ 0 = ρ 0 ∧ σ 1 = ρ 1 ∧
  σ 8 = (if ρ 9 + 1 = ρ 1 then 0 else 1) ∧
  σ 9 = (if ρ 9 + 1 = ρ 1 then 0 else ρ 9 + 1) ∧
  σ 10 = (if ρ 9 + 1 = ρ 1 then 0 else ρ 10) ∧
  σ 11 = (if ρ 9 + 1 = ρ 1 then 0 else ρ 11) ∧
  σ 12 = (if ρ 9 + 1 = ρ 1 then 0 else ρ 12) ∧
  (∀ mp, mp < 6 → ∀ key, N mp key =
    if mp = 3 ∧ ρ 9 + 1 = ρ 1 ∧ key = cpair (ρ 10) (ρ 12) then 1 else M mp key) ∧
  (∀ key, N 6 key = if ρ 9 + 1 = ρ 1 then 0 else M 6 key)

theorem scan_execution (ρ : Nat → Nat) (M : Nat → Nat → Nat) (κ : Nat → Nat → Nat)
    (hb : ρ 8 = 1) (hbool : BooleanSeven M)
    (hall : M 6 (ρ 9) = 1 → ∀ r v, M 4 (cpair (ρ 9) (cpair r v)) = 1 →
      r < ρ 10 → ρ 11 ≠ ρ 0 ∧ r ≤ ρ 11) :
    ScanEffect ρ M (sNext machine ρ M scanInput κ).1 (sNext machine ρ M scanInput κ).2 := by
  let V := (sView machine ρ M scanInput κ).1
  let N := withCarried machine M κ
  have vf (i : Nat) (hi : FixedRegister i) : V i = ρ i := view_fixed ρ M scanInput κ i hi
  have nl (mp : Nat) (hm : mp < 7) : N mp = M mp := carried_low M κ mp hm
  have hN : BooleanSeven N := by
    intro mp hm key
    rw [nl mp hm]
    exact hbool mp hm key
  obtain ⟨h73,h74,h75,h76,h77,h78,h79,h80⟩ := scan_actual_flags ρ M κ hb hall
  have hend : V 78 = 1 ↔ ρ 9 + 1 = ρ 1 := by
    change (sView machine ρ M scanInput κ).1 78 = 1 ↔ _
    rw [h78]
    by_cases he : ρ 9 + 1 = ρ 1 <;> simp [he]
  obtain ⟨s0,s1,s8,s9,s10,s11,s12⟩ := scan_register_effect V N h75 h76 h77
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [vf 0 (by decide)] at s0
    simpa only [sNext, sView, V, N] using s0
  · simp only [vf 1 (by decide)] at s1
    simpa only [sNext, sView, V, N] using s1
  · simp only [hend, vf 8 (by decide), hb] at s8
    simpa only [sNext, sView, V, N] using s8
  · simp only [hend, vf 9 (by decide)] at s9
    simpa only [sNext, sView, V, N] using s9
  · simp only [hend, vf 10 (by decide)] at s10
    simpa only [sNext, sView, V, N] using s10
  · simp only [hend, vf 11 (by decide)] at s11
    simpa only [sNext, sView, V, N] using s11
  · simp only [hend, vf 12 (by decide)] at s12
    simpa only [sNext, sView, V, N] using s12
  · intro mp hm key
    have h := scan_public_effect V N hN h73 h74 h79 h80 mp hm key
    simp only [hend, vf 10 (by decide), vf 12 (by decide), nl mp (by omega)] at h
    simpa only [sNext, sView, V, N] using h
  · intro key
    have h := scan_quorum_effect V N hN h75 h77 key
    simp only [hend, nl 6 (by decide)] at h
    simpa only [sNext, sView, V, N] using h

/-- An actual counted edge with its complete public/phase effect. The request
is constructed and all five counts realized; neither is an extra hypothesis. -/
theorem encoded_scan_step (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (hsize : 0 < ρ 1) (hb : ρ 8 = 1) (hbool : BooleanSeven M)
    (hall : M 6 (ρ 9) = 1 → ∀ r v, M 4 (cpair (ρ 9) (cpair r v)) = 1 →
      r < ρ 10 → ρ 11 ≠ ρ 0 ∧ r ≤ ρ 11) :
    ∃ y, CTransition machine declarations (ρ,M) y ∧ ScanEffect ρ M y.1 y.2 := by
  obtain ⟨κ,hκ⟩ := scan_counted_edge ρ M hsize
  exact ⟨_,hκ,scan_execution ρ M κ hb hbool hall⟩

#print axioms scan_execution
#print axioms encoded_scan_step
end Bapa.PaxosEprTarget
