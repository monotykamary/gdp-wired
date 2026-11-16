import RelationalFragment

namespace Bapa.Relational

/-- A duplicate-free finite enumeration of exactly the entries of a list.
    The list may contain aliases between constants and witnesses. -/
theorem list_enumeration {α : Type} (xs : List α) :
    ∃ (n : Nat) (enum : Fin n → α), n ≤ xs.length ∧
      (∀ i j, enum i = enum j → i = j) ∧
      (∀ x, x ∈ xs ↔ ∃ i, enum i = x) := by
  classical
  induction xs with
  | nil =>
      refine ⟨0, Fin.elim0, by simp, ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · intro x
        simp
  | cons x xs ih =>
      obtain ⟨n, enum, hn, hi, hc⟩ := ih
      by_cases hx : x ∈ xs
      · refine ⟨n, enum, by simp; omega, hi, ?_⟩
        intro y
        rw [List.mem_cons]
        constructor
        · rintro (rfl | hy)
          · exact (hc _).mp hx
          · exact (hc y).mp hy
        · intro h; exact Or.inr ((hc y).mpr h)
      · let next : Fin (n + 1) → α := Fin.cases x enum
        refine ⟨n + 1, next, by simp; omega, ?_, ?_⟩
        · intro i j
          refine Fin.cases ?_ (fun i' => ?_) i
          · refine Fin.cases ?_ (fun j' => ?_) j
            · intro _; rfl
            · intro hij
              exfalso
              apply hx
              have ht : enum j' ∈ xs := (hc _).mpr ⟨j', rfl⟩
              change x = enum j' at hij
              simpa [← hij] using ht
          · refine Fin.cases ?_ (fun j' => ?_) j
            · intro hij
              exfalso
              apply hx
              have ht : enum i' ∈ xs := (hc _).mpr ⟨i', rfl⟩
              change enum i' = x at hij
              simpa [hij] using ht
            · intro hij; exact congrArg Fin.succ (hi i' j' hij)
        · intro y
          rw [List.mem_cons]
          constructor
          · rintro (rfl | hy)
            · exact ⟨0, rfl⟩
            · obtain ⟨i, hi'⟩ := (hc y).mp hy
              exact ⟨i.succ, hi'⟩
          · rintro ⟨i, hi'⟩
            revert hi'
            refine Fin.cases ?_ (fun i' => ?_) i
            · intro h; exact Or.inl h.symm
            · intro h; exact Or.inr ((hc y).mpr ⟨i', h⟩)

variable {σ : Signature} {Γ : Context σ}

/-- Witness restriction preserves the complete EPR countermodel sentence.
    This has no numeric-certificate coverage hypothesis or conclusion. -/
theorem small_satisfiability (M : Model σ) (p : Matrix σ Γ) (hp : Satisfies M p) :
    ∃ N : Model σ, (∀ s, N.size s ≤ cutoff σ Γ s) ∧ Satisfies N p := by
  classical
  obtain ⟨w, hw⟩ := hp
  let support (s : SortId σ) : List (Fin (M.size s)) :=
    List.ofFn (M.constant s) ++ List.ofFn (w s) ++ [⟨0, M.nonempty s⟩]
  have he := fun s => list_enumeration (support s)
  let size (s : SortId σ) : Nat := Classical.choose (he s)
  let enum (s : SortId σ) : Fin (size s) → Fin (M.size s) :=
    Classical.choose (Classical.choose_spec (he s))
  have hp (s : SortId σ) : size s ≤ (support s).length ∧
      (∀ i j, enum s i = enum s j → i = j) ∧
      (∀ x, x ∈ support s ↔ ∃ i, enum s i = x) :=
    Classical.choose_spec (Classical.choose_spec (he s))
  have hmconst (s : SortId σ) (i : Fin (σ.constants s)) : M.constant s i ∈ support s := by
    simp only [support, List.mem_append, List.mem_ofFn]
    exact Or.inl (Or.inl ⟨i, rfl⟩)
  have hmw (s : SortId σ) (i : Fin (Γ.witnesses s)) : w s i ∈ support s := by
    simp only [support, List.mem_append, List.mem_ofFn]
    exact Or.inl (Or.inr ⟨i, rfl⟩)
  have hmf (s : SortId σ) : (⟨0, M.nonempty s⟩ : Fin (M.size s)) ∈ support s := by
    simp [support]
  have hpos (s : SortId σ) : 0 < size s := by
    obtain ⟨i, _⟩ := ((hp s).2.2 _).mp (hmf s)
    have := i.isLt
    omega
  let c (s : SortId σ) (i : Fin (σ.constants s)) : Fin (size s) :=
    Classical.choose (((hp s).2.2 _).mp (hmconst s i))
  let v (s : SortId σ) (i : Fin (Γ.witnesses s)) : Fin (size s) :=
    Classical.choose (((hp s).2.2 _).mp (hmw s i))
  let N : Model σ := {
    size := size
    nonempty := hpos
    constant := c
    relation := fun r args => M.relation r (fun i => enum _ (args i))
  }
  let e : Embedding N M := {
    map := enum
    injective := fun s => (hp s).2.1
    constants := fun s i => Classical.choose_spec (((hp s).2.2 _).mp (hmconst s i))
    relations := fun _ _ => Iff.rfl
  }
  refine ⟨N, ?_, v, ?_⟩
  · intro s
    have hb := (hp s).1
    simpa [N, support, cutoff, Nat.add_assoc] using hb
  · intro u
    apply (p.eval_embedding e v u).mpr
    have hvm : Assignment.map e v = w := by
      funext s i
      exact Classical.choose_spec (((hp s).2.2 _).mp (hmw s i))
    rw [hvm]
    exact hw (u.map e)

/-- A conditional logical lift, not a statement about any retained family. -/
theorem unsatisfiable_of_small (p : Matrix σ Γ)
    (hsmall : ∀ N : Model σ, (∀ s, N.size s ≤ cutoff σ Γ s) → ¬ Satisfies N p) :
    ∀ M : Model σ, ¬ Satisfies M p := by
  intro M h
  obtain ⟨N, hn, hp⟩ := small_satisfiability M p h
  exact hsmall N hn hp

#print axioms list_enumeration
#print axioms small_satisfiability
#print axioms unsatisfiable_of_small
end Bapa.Relational
