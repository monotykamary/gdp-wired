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
-- The bench (compare/bench): N requests from the LCG x' = (x * 1103515245 + 12345) mod 2^31, x from 42, each request's
-- c = x mod 16; b = 8N, m = 10. Prints the final s.
def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

def gen : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc.reverse
  | n + 1, x, acc => let y := lcg x; gen n y (y % 16 :: acc)

def main (args : List String) : IO Unit := do
  let n := ((args.head?.bind String.toNat?).getD 0)
  IO.println s!"{run (8 * n) 10 0 (gen n 42 [])}"
