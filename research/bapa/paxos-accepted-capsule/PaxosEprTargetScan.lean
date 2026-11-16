import PaxosEprTargetCounts
namespace Bapa.PaxosEprTarget
open Kern Bapa.FiniteSimulation

def scanInput : Nat → Nat := fun i => if i = 2 then 3 else 0

theorem scan_admitted (ρ : Nat → Nat) (M : Nat → Nat → Nat) (κ : Nat → Nat → Nat)
    (hsize : 0 < ρ 1) :
    evalC (sView machine ρ M scanInput κ).1 (sView machine ρ M scanInput κ).2 machine.f.m.assume = true := by
  simp [sView, machine, scanInput, decideFlags, applyS, flagSub, assoc, lookup,
    decideQ, withInputs, evalC, evalE, hsize]

/-- Existence includes all five actual count equations and actual admission. -/
theorem scan_counted_edge (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hsize : 0 < ρ 1) :
    ∃ κ, CTransition machine declarations (ρ,M) (sNext machine ρ M scanInput κ) := by
  obtain ⟨κ,_,hg⟩ := realize_counts ρ M scanInput (fun _ _ => 0)
  exact ⟨κ,counted_edge hg (scan_admitted ρ M κ hsize)⟩

/-- Row acceptance is genuinely unbounded in both round and value. -/
theorem row_flag_of_all (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hall : ∀ r v, M 4 (cpair (ρ 9) (cpair r v)) = 1 → r < ρ 10 →
      ρ 11 ≠ ρ 0 ∧ r ≤ ρ 11) : (sView machine ρ M ι κ).1 72 = 1 := by
  classical
  have hb : ∀ k : Nat → Nat,
      ¬ (M 4 (cpair (ρ 9) (cpair (k 133) (k 2000000))) = 1 ∧ k 133 < ρ 10) ∨
      (ρ 11 ≠ ρ 0 ∧ k 133 ≤ ρ 11) := by
    intro k
    by_cases h : M 4 (cpair (ρ 9) (cpair (k 133) (k 2000000))) = 1 ∧ k 133 < ρ 10
    · exact .inr (hall _ _ h.1 h.2)
    · exact .inl h
  have he : (if ∀ k : Nat → Nat,
      ¬ (M 4 (cpair (ρ 9) (cpair (k 133) (k 2000000))) = 1 ∧ k 133 < ρ 10) ∨
      (ρ 11 ≠ ρ 0 ∧ k 133 ≤ ρ 11) then (1 : Nat) else 0) = 1 := by
    rw [if_pos hb]
  simpa [sView, machine, decideFlags, applyS, flagSub, assoc, lookup, decideQ,
    withInputs, holdsC, evalE, atKeys, withCarried] using he

/-- Scan flags on a pre-flag view; no public update other than final Proposal. -/
theorem scan_plain_flags (D : Nat → Nat) (N : Nat → Nat → Nat)
    (hop : D 2 = 3) (hbusy : D 8 = 1)
    (hrow : N 6 (D 9) = 1 → D 72 = 1) :
    let V := decideFlags machine.f.flags D N
    V 73 = 0 ∧ V 74 = 0 ∧ V 75 = 0 ∧ V 76 = 1 ∧ V 77 = 0 ∧
      V 78 = (if D 9 + 1 = D 1 then 1 else 0) ∧ V 79 = 0 ∧ V 80 = 0 := by
  by_cases he : D 9 + 1 = D 1
  all_goals
    by_cases hq : N 6 (D 9) = 1
    · have hr := hrow hq
      simp [decideFlags, machine, applyS, flagSub, assoc, lookup, evalE, evalC, hop, hbusy, hq, hr, he]
    · simp [decideFlags, machine, applyS, flagSub, assoc, lookup, evalE, evalC, hop, hbusy, hq, he]

#print axioms scan_admitted
#print axioms scan_counted_edge
#print axioms row_flag_of_all
#print axioms scan_plain_flags
end Bapa.PaxosEprTarget
