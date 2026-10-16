-- Rule 1, the budget, in plain Lean 4 (core only): s from 0; a request of cost c adds min c m while s < b.
-- Law: s ≤ b + m after any list of requests, proven by hand (induction on the list, omega per step).

-- --- rule
def step (b m s c : Nat) : Nat := if s < b then s + min c m else s

def run (b m s : Nat) : List Nat → Nat
  | [] => s
  | c :: cs => run b m (step b m s c) cs

-- --- laws
theorem bounded (b m : Nat) (cs : List Nat) : run b m 0 cs ≤ b + m := by
-- --- proofs
  suffices h : ∀ s, s ≤ b + m → run b m s cs ≤ b + m from h 0 (Nat.zero_le _)
  induction cs with
  | nil => intro s hs; exact hs
  | cons c cs ih =>
    intro s hs
    apply ih
    have := Nat.min_le_right c m
    unfold step; split <;> omega

-- --- run
#eval run 10 4 0 [3, 9, 1, 7, 2]
