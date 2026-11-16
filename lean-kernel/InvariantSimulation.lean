import FiniteSimulation

/-! Invariant-restricted, one-step simulation. The invariant comes from the
checked target family, not from an extra premise on source executions. -/
namespace Bapa.InvariantSimulation
open Kern Bapa.FiniteSimulation

/-- Local correspondence is required only where a checked target invariant
holds. In contrast to `SourceInclusion`, this makes no all-state claim. -/
structure RestrictedInclusion (s t : SMachine) (Inv : KState → Prop) : Prop where
  initial : ∀ x, Initial s x → Initial t x
  admission : ∀ ρ M ι κ, Inv (ρ,M) →
    evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true →
    evalC (sView t ρ M ι κ).1 (sView t ρ M ι κ).2 t.f.m.assume = true
  next : ∀ ρ M ι κ, Inv (ρ,M) →
    evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true →
    sNext s ρ M ι κ = sNext t ρ M ι κ

/-- Boundary states coincide and satisfy the target's checked invariant. -/
def Relation (Inv : KState → Prop) (x y : KState) : Prop := x = y ∧ Inv y

/-- The family invariant is a theorem about target reachability. It is never
inserted into the source assumption or the source theorem's hypotheses. -/
theorem RestrictedInclusion.simulation {s t : SMachine} {Inv : KState → Prop}
    (hinc : RestrictedInclusion s t Inv)
    (checked : ∀ ρ M, SReach t ρ M → Inv (ρ,M)) :
    SSimulation s t (Relation Inv) where
  initial := by
    intro x hx
    have ht : Reachable (Initial t) (STransition t) x := .initial (hinc.initial x hx)
    exact ⟨x, ht, rfl, checked x.1 x.2 (sreach_out ht)⟩
  matching := by
    intro x x' y _ hy hrel hedge
    rcases hrel with ⟨heq, hinv⟩
    subst y
    rcases hedge with ⟨ι, κ, ha, rfl⟩
    have hta := hinc.admission x.1 x.2 ι κ hinv ha
    have hn := hinc.next x.1 x.2 ι κ hinv ha
    have edge : STransition t x (sNext t x.1 x.2 ι κ) := ⟨ι, κ, hta, rfl⟩
    have reach := Reachable.next hy edge
    refine ⟨sNext t x.1 x.2 ι κ, .next (.refl x) edge, hn, ?_⟩
    exact checked _ _ (sreach_out reach)

theorem RestrictedInclusion.sreach {s t : SMachine} {Inv : KState → Prop}
    (hinc : RestrictedInclusion s t Inv)
    (checked : ∀ ρ M, SReach t ρ M → Inv (ρ,M)) {ρ M}
    (hr : SReach s ρ M) : SReach t ρ M := by
  obtain ⟨y, hy, hrel⟩ := sprojected_reach (hinc.simulation checked) hr
  rcases hrel with ⟨rfl, _⟩
  exact hy

/-- Transfer the exact source conclusion; only the target proof supplies the
invariant. No bounded-key premise or strengthened source assumption occurs. -/
theorem RestrictedInclusion.law {s t : SMachine} {Inv : KState → Prop}
    (hinc : RestrictedInclusion s t Inv)
    (checked : ∀ ρ M, SReach t ρ M → Inv (ρ,M))
    (P : (Nat → Nat) → (Nat → Nat → Nat) → Prop)
    (target : ∀ ρ M, SReach t ρ M → P ρ M) :
    ∀ ρ M, SReach s ρ M → P ρ M :=
  fun ρ M hr => target ρ M (hinc.sreach checked hr)

/-- A Boolean map bound is sufficient for threshold and Boolean-normalized
reads to coincide. This elementary implication is false without the bound. -/
theorem threshold_eq_one {n : Nat} (h : n ≤ 1) : (1 ≤ n ↔ n = 1) := by omega

theorem boolean_stutter {n : Nat} (h : n ≤ 1) : (if n = 1 then 1 else 0) = n := by
  split <;> omega

#print axioms RestrictedInclusion.simulation
#print axioms RestrictedInclusion.sreach
#print axioms RestrictedInclusion.law
#print axioms threshold_eq_one
#print axioms boolean_stutter
end Bapa.InvariantSimulation
