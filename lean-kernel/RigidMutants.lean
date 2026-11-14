import Rigid

/-! Countermodels to weakened Skolem premises: neither dropped ranges,
omitted conjuncts, nor diagonal-only coverage establishes the source axiom. -/
namespace Kern.Rigid.Mutants

example : (∃ meet : Nat → Nat → Nat, ∀ q₁ q₂, q₁ < 1 → q₂ < 1 →
    (True ∧ True)) ∧ ¬ BoundedIntersects 0 1 (fun _ _ => True) := by
  constructor
  · exact ⟨fun _ _ => 0, fun _ _ _ _ => ⟨trivial, trivial⟩⟩
  · intro h
    obtain ⟨n, hn, _⟩ := h 0 0 (by decide) (by decide)
    omega

example : (∃ meet : Nat → Nat → Nat, ∀ q₁ q₂, q₁ < 2 → q₂ < 2 →
    meet q₁ q₂ < 2 ∧ meet q₁ q₂ = q₁) ∧
    ¬ BoundedIntersects 2 2 (fun n q => n = q) := by
  constructor
  · exact ⟨fun q₁ _ => q₁, fun _ _ h₁ _ => ⟨h₁, rfl⟩⟩
  · intro h
    obtain ⟨n, _, h₀, h₁⟩ := h 0 1 (by decide) (by decide)
    omega

example : (∀ q, q < 2 → ∃ n, n < 2 ∧ n = q ∧ n = q) ∧
    ¬ BoundedIntersects 2 2 (fun n q => n = q) := by
  constructor
  · exact fun q hq => ⟨q, hq, rfl, rfl⟩
  · intro h
    obtain ⟨n, _, h₀, h₁⟩ := h 0 1 (by decide) (by decide)
    omega

end Kern.Rigid.Mutants
