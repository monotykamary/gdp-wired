-- Rule 2, per-key caps, in plain Lean 4 (core only): the state is the list of grants (acct, day); a request is
-- granted iff ok and its account has no grant yet and its day has fewer than d. Laws: at every key k, at most one
-- grant per account and at most d per day, after any list of requests. Proven by hand.

-- --- rule
structure Req where
  ok : Bool
  acct : Nat
  day : Nat

def cntAcct (k : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (a, _) :: g => (if a = k then 1 else 0) + cntAcct k g

def cntDay (k : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (_, y) :: g => (if y = k then 1 else 0) + cntDay k g

def step (d : Nat) (g : List (Nat × Nat)) (r : Req) : List (Nat × Nat) :=
  if r.ok = true ∧ cntAcct r.acct g < 1 ∧ cntDay r.day g < d then (r.acct, r.day) :: g else g

def run (d : Nat) (g : List (Nat × Nat)) : List Req → List (Nat × Nat)
  | [] => g
  | r :: rs => run d (step d g r) rs

-- --- laws
theorem once_per_acct (d : Nat) (rs : List Req) (k : Nat) : cntAcct k (run d [] rs) ≤ 1 := by
-- --- proofs
  suffices h : ∀ g, cntAcct k g ≤ 1 → cntAcct k (run d g rs) ≤ 1 from h [] (by simp [cntAcct])
  induction rs with
  | nil => intro g hg; exact hg
  | cons r rs ih =>
    intro g hg
    apply ih
    unfold step
    split
    · rename_i h
      obtain ⟨_, h1, h2⟩ := h
      simp only [cntAcct]
      by_cases e : r.acct = k
      · rw [ite_eq_left e]; rw [e] at h1; omega
      · rw [ite_eq_right e]; omega
    · exact hg

-- --- laws
theorem day_cap (d : Nat) (rs : List Req) (k : Nat) : cntDay k (run d [] rs) ≤ d := by
-- --- proofs
  suffices h : ∀ g, cntDay k g ≤ d → cntDay k (run d g rs) ≤ d from h [] (by simp [cntDay])
  induction rs with
  | nil => intro g hg; exact hg
  | cons r rs ih =>
    intro g hg
    apply ih
    unfold step
    split
    · rename_i h
      obtain ⟨_, h1, h2⟩ := h
      simp only [cntDay]
      by_cases e : r.day = k
      · rw [ite_eq_left e]; rw [e] at h2; omega
      · rw [ite_eq_right e]; omega
    · exact hg

-- --- run
-- The bench (compare/bench): N requests from the LCG x' = (x * 1103515245 + 12345) mod 2^31, x from 42, each request's
-- acct = x mod 1000, day = x mod 365, ok = x mod 4 != 0; d = 3. Prints the number of grants, the sum of their accts and
-- the sum of their days.
def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

def gen : Nat → Nat → List Req → List Req
  | 0, _, acc => acc.reverse
  | n + 1, x, acc => let y := lcg x; gen n y (⟨y % 4 != 0, y % 1000, y % 365⟩ :: acc)

def sums (g : List (Nat × Nat)) : Nat × Nat × Nat :=
  g.foldl (fun (n, a, d) (x, y) => (n + 1, a + x, d + y)) (0, 0, 0)

def main (args : List String) : IO Unit := do
  let n := ((args.head?.bind String.toNat?).getD 0)
  let (k, a, d) := sums (run 3 [] (gen n 42 []))
  IO.println s!"{k} {a} {d}"
