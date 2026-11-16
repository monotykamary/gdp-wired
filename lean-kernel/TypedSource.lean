import SourceInclusion
import BoundGhost

namespace Kern.TypedSource
/-- The public existential conclusion follows from a semantic law of the
    ghost extension. The certificate may have been checked on a larger machine
    reached by SourceInclusion; no checker premise for the smaller one is needed. -/
theorem ex_of_holds (g : SGhostedM) (hg : smghostOk g = true)
    (e : SEntry) (σ : List (Nat × E)) (c : C)
    (hsub : e.law.holds = substC σ c)
    (hav : avoids (g.vars.filter fun v => !(σ.map (·.1)).contains v) c = true)
    (ham : avoidsMaps g.maps c = true)
    (hall : ∀ ρ M, SReach g.full ρ M → e.Holds ρ M) :
    ∀ ρ M, SReach g.orig ρ M → ExHolds c e.law.key (σ.map (·.1)) M e.keys2 ρ := by
  intro ρ M hr
  obtain ⟨ρg, Mg, hrg, hag, hmag⟩ := smghost_reach g hg hr
  have h := hall ρg Mg hrg
  simp only [SEntry.Holds] at h
  have go : ∀ (gs : List Nat) (ρg ρ : Nat → Nat), Agree g.vars ρg ρ →
      holdsOver e.law Mg gs ρg → ExHolds c e.law.key (σ.map (·.1)) M gs ρ := by
    intro gs
    induction gs with
    | nil =>
      intro ρg ρ hag h
      simp only [holdsOver, MLaw.Holds] at h
      cases hk : e.law.key with
      | none =>
        simp only [hk, hsub] at h
        simp only [ExHolds]
        exact some_of_subst_bound_apart σ c hav ham hag hmag h
      | some kv =>
        simp only [hk, hsub] at h
        simp only [ExHolds]
        intro v
        exact some_of_subst_bound_apart σ c hav ham (upd_agree hag kv v) hmag (h v)
    | cons k gs ih =>
      intro ρg ρ hag h w
      exact ih (upd ρg k w) (upd ρ k w) (upd_agree hag k w) (h w)
  exact go e.keys2 ρg ρ hag h
end Kern.TypedSource
#print axioms Kern.TypedSource.ex_of_holds
