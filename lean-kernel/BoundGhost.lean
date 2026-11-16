import GhostMap

namespace Kern

/-- Equal initial values, or a shared update at the key, suffice for equal results. -/
theorem updAll_congr_at {X X' : Nat → Nat} {i : Nat} (l : List (Nat × Nat))
    (h : X i = X' i ∨ i ∈ l.map (·.1)) : updAll X l i = updAll X' l i := by
  induction l generalizing X X' with
  | nil => simpa [updAll] using h
  | cons p ps ih =>
    apply ih
    simp only [List.map_cons, List.mem_cons] at h
    rcases h with h | h | h
    · left; simp only [upd]; split <;> simp_all
    · left; simp [upd, h]
    · exact Or.inr h

/-- Shared updates make bound keys agree; other non-ghost keys already agreed. -/
theorem updAll_agree_bound {V : List Nat} {X X' : Nat → Nat} (h : Agree V X X')
    (l : List (Nat × Nat)) : Agree (V.filter fun v => !(l.map (·.1)).contains v) (updAll X l) (updAll X' l) := by
  intro i hi
  apply updAll_congr_at
  by_cases hk : i ∈ l.map (·.1)
  · exact Or.inr hk
  · left
    apply h i
    intro hv
    apply hi
    apply List.mem_filter.mpr
    exact ⟨hv, by simpa using hk⟩

theorem some_of_subst_bound_apart {V MS : List Nat} (σ : List (Nat × E)) (c : C)
    (hav : avoids (V.filter fun v => !(σ.map (·.1)).contains v) c = true)
    (ham : avoidsMaps MS c = true) {ρg ρ : Nat → Nat} {Mg M : Nat → Nat → Nat}
    (hag : Agree V ρg ρ) (hmag : ∀ mp, mp ∉ MS → Mg mp = M mp)
    (h : evalC ρg Mg (substC σ c) = true) :
    ∃ f : Nat → Nat, evalC (updAll ρ ((σ.map (·.1)).map fun i => (i, f i))) M c = true := by
  refine ⟨fun i => applyS σ ρg Mg i, ?_⟩
  have h1 := some_of_subst σ c ρg Mg h
  have hx := updAll_agree_bound hag ((σ.map (·.1)).map fun i => (i, applyS σ ρg Mg i))
  have hx' : Agree (V.filter fun v => !(σ.map (·.1)).contains v)
      (updAll ρg ((σ.map (·.1)).map fun i => (i, applyS σ ρg Mg i)))
      (updAll ρ ((σ.map (·.1)).map fun i => (i, applyS σ ρg Mg i))) := by
    simpa [List.map_map, Function.comp_def] using hx
  rw [congrC _ _ M _ (fun i hi => (hx' i (avoids_occ hav hi)).symm),
    congrMC _ M Mg _ (fun mp hmp => (hmag mp (avoidsMaps_occ ham hmp)).symm)]
  exact h1

theorem forall_some_of_ghostsubst_bound (g : SGhostedM) (hg : smghostOk g = true) (ps : List SEntry) (hl : checkSMachine g.full ps = true)
    (e : SEntry) (he : e ∈ ps) (σ : List (Nat × E)) (c : C) (hsub : e.law.holds = substC σ c)
    (hav : avoids (g.vars.filter fun v => !(σ.map (·.1)).contains v) c = true) (ham : avoidsMaps g.maps c = true) :
    ∀ ρ M, SReach g.orig ρ M → ExHolds c e.law.key (σ.map (·.1)) M e.keys2 ρ := by
  intro ρ M hr
  obtain ⟨ρg, Mg, hrg, hag, hmag⟩ := smghost_reach g hg hr
  have hall := smachine_sound g.full ps hl ρg Mg hrg e he
  simp only [SEntry.Holds] at hall
  -- (along the further keys, each at the same value on both sides)
  have go : ∀ (gs : List Nat) (ρg ρ : Nat → Nat), Agree g.vars ρg ρ → holdsOver e.law Mg gs ρg → ExHolds c e.law.key (σ.map (·.1)) M gs ρ := by
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
  exact go e.keys2 ρg ρ hag hall

end Kern

#print axioms Kern.updAll_congr_at
#print axioms Kern.some_of_subst_bound_apart
#print axioms Kern.forall_some_of_ghostsubst_bound
