-- Rule 3, the sliding-window limit, in plain Lean 4 (core only): the state is the log of requests (forced, t); a
-- request is admitted iff not forced and seen + 1 ≤ c, seen counting the logged requests with t < e.t + w; forced
-- requests always go through; both are logged. Law: at every now, the unforced (so admitted) logged requests in the
-- window ending at now (e.t ≤ now < e.t + w) number at most c, after any list of requests. Proven by hand.

-- --- rule
structure Ent where
  forced : Bool
  t : Nat

def seen (w t : Nat) : List Ent → Nat
  | [] => 0
  | e :: l => (if t < e.t + w then 1 else 0) + seen w t l

def step (w c : Nat) (l : List Ent) (r : Ent) : List Ent :=
  if r.forced = true then r :: l
  else if seen w r.t l + 1 ≤ c then r :: l
  else l

def run (w c : Nat) (l : List Ent) : List Ent → List Ent
  | [] => l
  | r :: rs => run w c (step w c l r) rs

-- --- laws
def ours (w now : Nat) : List Ent → Nat
  | [] => 0
  | e :: l => (if e.forced = false ∧ e.t ≤ now ∧ now < e.t + w then 1 else 0) + ours w now l

theorem ceiling (w c now : Nat) (rs : List Ent) : ours w now (run w c [] rs) ≤ c := by
-- --- proofs
  -- every record ours counts at now is one seen counts at any t ≤ now
  have le_seen : ∀ t l, t ≤ now → ours w now l ≤ seen w t l := by
    intro t l ht
    induction l with
    | nil => simp [ours, seen]
    | cons e l ih =>
      simp only [ours, seen]
      by_cases h1 : e.forced = false ∧ e.t ≤ now ∧ now < e.t + w
      · have h2 : t < e.t + w := by have := h1.2.2; omega
        rw [ite_eq_left h1, ite_eq_left h2]; omega
      · rw [ite_eq_right h1]; split <;> omega
  suffices h : ∀ l, ours w now l ≤ c → ours w now (run w c l rs) ≤ c from h [] (by simp [ours])
  induction rs with
  | nil => intro l hl; exact hl
  | cons r rs ih =>
    intro l hl
    apply ih
    unfold step
    split
    · rename_i hf
      have h1 : ¬(r.forced = false ∧ r.t ≤ now ∧ now < r.t + w) := by simp [hf]
      simp only [ours]; rw [ite_eq_right h1]; omega
    · split
      · rename_i hf hs
        simp only [ours]
        by_cases h1 : r.forced = false ∧ r.t ≤ now ∧ now < r.t + w
        · have := le_seen r.t l h1.2.1
          rw [ite_eq_left h1]; omega
        · rw [ite_eq_right h1]; omega
      · exact hl

-- --- run
#eval (run 10 2 [] [⟨false, 1⟩, ⟨false, 3⟩, ⟨false, 4⟩, ⟨true, 5⟩, ⟨false, 12⟩]).length
