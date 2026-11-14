import Bounded

namespace Kern.Bounded
-- Concrete countermodels of every weakened premise; these are checked proofs,
-- not assertions accepted because a deliberately broken file failed to parse.
example : ¬ (∀ k : Nat, k < 0 → False) → False := by simp
example : ¬ (∀ (p : Nat → Prop), (∀ k, k < 0 → p k) → p 0) := by
  intro h
  exact h (fun _ => False) (by intro k hk; omega)
example : ¬ (∃ k : Nat, k < 0 ∧ True) := by
  rintro ⟨k, hk, _⟩; omega
example : allBelow (fun _ => false) 0 = true := rfl
example : anyBelow (fun _ => true) 0 = false := rfl
example : allBelow (fun k => decide (k < 2)) 2 = true ∧
    allBelow (fun k => decide (k < 2)) 3 = false := by decide
-- Dropping freshness changes a free read of the witness.
example : evalC (fun _ => 0) (fun _ _ => 0) (.eq (.var 1) (.const 0)) = true ∧
    evalC (upd (fun _ => 0) 1 1) (fun _ _ => 0) (.eq (.var 1) (.const 0)) = false := by decide
-- A binder-dependent bound does not denote the original finite domain.
example : (∀ k : Nat, holdsC (upd (fun _ => 1) 0 k) (fun _ _ => 0)
    (guard 0 (.var 0) (.eq (.const 0) (.const 1)))) ∧
    allBelow (fun _ => false) 1 = false := by
  constructor
  · intro k; simp [guard, holdsC, evalE, upd]
  · rfl
-- Counting the overlap twice is false already in a one-element domain.
example : card (fun _ => true) 1 ≠
    card (fun _ => true && true) 1 + card (fun _ => true) 1 := by decide
end Kern.Bounded
