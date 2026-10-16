-- Structural recursion over a list, the kind of law the step-machine language can't express: grind with the defs.
def total : List Nat → Nat
  | [] => 0
  | c :: cs => c + total cs
def capped (m : Nat) : List Nat → List Nat
  | [] => []
  | c :: cs => min c m :: capped m cs
theorem total_capped (m : Nat) (cs : List Nat) : total (capped m cs) ≤ m * cs.length := by
  induction cs with
  | nil => simp [capped, total]
  | cons c cs ih => simp only [capped, total, List.length_cons]; grind
-- Nonlinear: a price times a quantity stays under a cap, from bounds on both.
example (p q : Nat) (hp : p ≤ 100) (hq : q ≤ 50) : p * q ≤ 5000 := by
  have := Nat.mul_le_mul hp hq
  omega
