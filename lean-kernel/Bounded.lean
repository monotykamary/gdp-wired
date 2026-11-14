import Count

/-!
Finite-domain quantifiers, conservatively elaborated to the existing condition language.
A bounded universal is `∀ k, k < n → body k`. Its guard is part of the body sent to
Sets.closingHyps, not an unchecked annotation. No restriction on reads in `body` is needed.
This module adds no axiom, proof-tree constructor, or change to the legacy checker.
-/
namespace Kern.Bounded

/-- The executable enumeration used by a finite universal. -/
def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow p n && p n

def anyBelow (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => anyBelow p n || p n

theorem allBelow_iff (p : Nat → Bool) (n : Nat) :
    allBelow p n = true ↔ ∀ k, k < n → p k = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ k hk
      by_cases he : k = n
      · simpa [he] using hn
      · exact h k (by omega)
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

theorem anyBelow_iff (p : Nat → Bool) (n : Nat) :
    anyBelow p n = true ↔ ∃ k, k < n ∧ p k = true := by
  induction n with
  | zero => simp [anyBelow]
  | succ n ih =>
    simp only [anyBelow, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk, hp⟩ | hp)
      · exact ⟨k, by omega, hp⟩
      · exact ⟨n, by omega, hp⟩
    · rintro ⟨k, hk, hp⟩
      by_cases he : k = n
      · right; simpa [he] using hp
      · exact Or.inl ⟨k, by omega, hp⟩

/-- The syntax passed unchanged to the existing universal instance/closing rules. -/
def guard (key : Nat) (bound : E) (body : C) : C :=
  .or (.not (.lt (.var key) bound)) body

theorem evalE_upd_of_fresh (X : Nat → Nat) (M : Nat → Nat → Nat)
    (e : E) (key value : Nat) (h : occE key e = false) :
    evalE (upd X key value) M e = evalE X M e := by
  apply congrE
  intro i hi
  have hne : i ≠ key := by intro he; subst i; simp [h] at hi
  simp [upd, hne]

theorem guard_iff (X : Nat → Nat) (M : Nat → Nat → Nat)
    (key value : Nat) (bound : E) (body : C) (h : occE key bound = false) :
    holdsC (upd X key value) M (guard key bound body) ↔
      (value < evalE X M bound → holdsC (upd X key value) M body) := by
  rw [← evalC_iff, ← evalC_iff]
  simp [guard, evalC, evalE, upd, evalE_upd_of_fresh X M bound key value h]
  by_cases hp : evalC (upd X key value) M body = true <;> simp [hp]

theorem boundedAll_iff (X : Nat → Nat) (M : Nat → Nat → Nat)
    (key : Nat) (bound : E) (body : C) (h : occE key bound = false) :
    allBelow (fun k => evalC (upd X key k) M body) (evalE X M bound) = true ↔
      ∀ k, holdsC (upd X key k) M (guard key bound body) := by
  rw [allBelow_iff]
  simp only [guard_iff X M key _ bound body h, evalC_iff]

theorem boundedAny_iff (X : Nat → Nat) (M : Nat → Nat → Nat)
    (key : Nat) (bound : E) (body : C) :
    anyBelow (fun k => evalC (upd X key k) M body) (evalE X M bound) = true ↔
      ∃ k, k < evalE X M bound ∧ holdsC (upd X key k) M body := by
  rw [anyBelow_iff]
  simp only [evalC_iff]

theorem applyS_one (X : Nat → Nat) (M : Nat → Nat → Nat) (key : Nat) (t : E) :
    applyS [(key, t)] X M = upd X key (evalE X M t) := by
  funext i
  by_cases hi : i = key
  · simp [applyS, assoc, lookup, upd, hi]
  · simp [applyS, assoc, lookup, upd, hi, Ne.symm hi]

/-- An out-of-domain term never gives an unconditional instance. -/
theorem bounded_instance (X : Nat → Nat) (M : Nat → Nat → Nat)
    (key : Nat) (bound t : E) (body : C)
    (h : ∀ k, k < evalE X M bound → holdsC (upd X key k) M body)
    (ht : evalE X M t < evalE X M bound) :
    holdsC X M (substC [(key, t)] body) := by
  rw [← evalC_iff, subst_evalC, applyS_one, evalC_iff]
  exact h _ ht

theorem bounded_counterexample (X : Nat → Nat) (M : Nat → Nat → Nat)
    (key : Nat) (bound : E) (body : C)
    (h : ¬ ∀ k, k < evalE X M bound → holdsC (upd X key k) M body) :
    ∃ w, w < evalE X M bound ∧ ¬ holdsC (upd X key w) M body := by
  apply Classical.byContradiction
  intro hno
  apply h
  intro k hk
  apply Classical.byContradiction
  intro hp
  exact hno ⟨k, hk, hp⟩

/-- Existential lowering uses the counterexample to the guarded *negated* body. -/
theorem exists_as_not_all (n : Nat) (p : Nat → Prop) :
    (∃ k, k < n ∧ p k) ↔ ¬ (∀ k, k < n → ¬ p k) := by
  constructor
  · rintro ⟨k, hk, hp⟩ hall
    exact hall k hk hp
  · intro h
    apply Classical.byContradiction
    intro hno
    apply h
    intro k hk hp
    exact hno ⟨k, hk, hp⟩

/-- Changing a fresh witness variable does not capture a read in the body. -/
theorem fresh_subst (X : Nat → Nat) (M : Nat → Nat → Nat)
    (key witness value : Nat) (body : C) (fresh : occC witness body = false) :
    holdsC (upd X witness value) M (substC [(key, .var witness)] body) ↔
      holdsC (upd X key value) M body := by
  rw [← evalC_iff, ← evalC_iff, subst_evalC, applyS_one]
  apply Iff.of_eq
  congr 1
  apply congrC
  intro i hi
  have hn : i ≠ witness := by intro he; subst i; simp [fresh] at hi
  simp [evalE, upd, hn]

/-- A fresh existential witness is bounded in the original (immutable) domain. -/
theorem bounded_witness (X : Nat → Nat) (M : Nat → Nat → Nat)
    (key witness : Nat) (bound : E) (body : C)
    (freshBody : occC witness body = false) (freshBound : occE witness bound = false)
    (h : ∃ k, k < evalE X M bound ∧ holdsC (upd X key k) M body) :
    ∃ value, value < evalE (upd X witness value) M bound ∧
      holdsC (upd X witness value) M (substC [(key, .var witness)] body) := by
  obtain ⟨value, hv, hb⟩ := h
  refine ⟨value, ?_, (fresh_subst X M key witness value body freshBody).mpr hb⟩
  simpa only [evalE_upd_of_fresh X M bound witness value freshBound] using hv

/-- A false guarded instance includes the domain bound, not just a false body. -/
theorem guard_failure_iff (X : Nat → Nat) (M : Nat → Nat → Nat)
    (key value : Nat) (bound : E) (body : C) (h : occE key bound = false) :
    (¬ holdsC (upd X key value) M (guard key bound body)) ↔
      value < evalE X M bound ∧ ¬ holdsC (upd X key value) M body := by
  rw [guard_iff X M key value bound body h]
  constructor
  · intro hno
    have hv : value < evalE X M bound := by
      apply Classical.byContradiction
      intro hv
      exact hno (fun h => False.elim (hv h))
    exact ⟨hv, fun hp => hno (fun _ => hp)⟩
  · rintro ⟨hv, hp⟩ hbody
    exact hp (hbody hv)

/-- The existing false-flag witness, freshly substituted in the actual guard,
    implies both its bound and a counterexample body in the new environment. -/
theorem fresh_guard_failure (X : Nat → Nat) (M : Nat → Nat → Nat)
    (key witness value : Nat) (bound : E) (body : C)
    (fresh : occC witness (guard key bound body) = false)
    (independent : occE key bound = false) :
    (¬ holdsC (upd X witness value) M (substC [(key, .var witness)] (guard key bound body))) ↔
      value < evalE X M bound ∧ ¬ holdsC (upd X key value) M body := by
  rw [fresh_subst X M key witness value (guard key bound body) fresh]
  exact guard_failure_iff X M key value bound body independent

#print axioms guard_failure_iff
#print axioms fresh_guard_failure

theorem bounded_empty (p : Nat → Bool) : allBelow p 0 = true ∧ anyBelow p 0 = false := by
  exact ⟨rfl, rfl⟩

/-- Venn regions, derived pointwise with the same sum used by counted_sound. -/
theorem venn_left (x s : Nat → Bool) (n : Nat) :
    card x n = card (fun k => x k && s k) n + card (fun k => x k && !s k) n := by
  unfold card
  rw [← sumBelow_add]
  apply sumBelow_congr
  intro k _
  cases hx : x k <;> cases hs : s k <;> simp [hx, hs]

theorem venn_right (x s : Nat → Bool) (n : Nat) :
    card s n = card (fun k => x k && s k) n + card (fun k => !x k && s k) n := by
  unfold card
  rw [← sumBelow_add]
  apply sumBelow_congr
  intro k _
  cases hx : x k <;> cases hs : s k <;> simp [hx, hs]

theorem venn_union_bound (x s : Nat → Bool) (n : Nat) :
    card (fun k => x k && s k) n + card (fun k => x k && !s k) n +
      card (fun k => !x k && s k) n ≤ n := by
  unfold card
  rw [← sumBelow_add, ← sumBelow_add]
  have h := sumBelow_mono n (f := fun k =>
    (if x k && s k then 1 else 0) + (if x k && !s k then 1 else 0) +
    (if !x k && s k then 1 else 0)) (g := fun _ => 1) (by
      intro k _; cases x k <;> cases s k <;> decide)
  simpa [sumBelow_const] using h

#print axioms allBelow_iff
#print axioms anyBelow_iff
#print axioms guard_iff
#print axioms boundedAll_iff
#print axioms boundedAny_iff
#print axioms bounded_instance
#print axioms bounded_counterexample
#print axioms exists_as_not_all
#print axioms fresh_subst
#print axioms bounded_witness
#print axioms bounded_empty
#print axioms venn_left
#print axioms venn_right
#print axioms venn_union_bound
end Kern.Bounded
