import IntegerPrimitives

/-! The exact little-endian addition loop from core/fixed-integers.ts: add each
limb and incoming carry, emit remainder, propagate quotient. For 16/32/64
bits there are respectively one/two/four radix-65536 limbs. This proof is
about that loop, not merely about BitVec addition of already assembled words. -/
namespace FixedLimbBridge

def radix : Nat := 65536

/-- Little-endian polynomial, including the empty word. -/
def assemble : List Nat → Nat
  | [] => 0
  | x :: xs => x + radix * assemble xs

/-- The implementation's addRaw, restricted to equally long limb arrays. -/
def addCarry : List Nat → List Nat → Nat → List Nat × Nat
  | [], [], c => ([], c)
  | x :: xs, y :: ys, c =>
    let s := x + y + c
    let rest := addCarry xs ys (s / radix)
    (s % radix :: rest.1, rest.2)
  | _, _, c => ([], c)

/-- Each loop iteration reconstructs the exact sum from remainder and carry. -/
theorem digit_carry (s : Nat) : s % radix + radix * (s / radix) = s := by
  exact Nat.mod_add_div s radix

/-- Polynomial reconstruction for *the actual recursive carry algorithm*.
No boundedness assumption is needed for this exact identity. -/
theorem addCarry_reconstruct (a b : List Nat) (c : Nat)
    (h : a.length = b.length) :
    assemble (addCarry a b c).1 + radix ^ a.length * (addCarry a b c).2 =
      assemble a + assemble b + c := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil => simp [addCarry, assemble]
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      have ht : xs.length = ys.length := Nat.succ.inj h
      let s := x + y + c
      let rest := addCarry xs ys (s / radix)
      have hr : assemble rest.1 + radix ^ xs.length * rest.2 =
          assemble xs + assemble ys + s / radix := ih ys (s / radix) ht
      change s % radix + radix * assemble rest.1 +
          radix ^ (xs.length + 1) * rest.2 =
          (x + radix * assemble xs) + (y + radix * assemble ys) + c
      rw [Nat.pow_succ]
      calc
        s % radix + radix * assemble rest.1 +
            (radix ^ xs.length * radix) * rest.2 =
            s % radix + radix * (assemble rest.1 + radix ^ xs.length * rest.2) := by
              simp only [Nat.mul_add, ← Nat.mul_assoc]
              ac_rfl
        _ = s % radix + radix * (assemble xs + assemble ys + s / radix) := by rw [hr]
        _ = (x + radix * assemble xs) + (y + radix * assemble ys) + c := by
          have hd := digit_carry s
          dsimp [s, radix] at hd ⊢
          omega

/-- The loop emits exactly one bounded digit per input digit. -/
theorem addCarry_digits (a b : List Nat) (c : Nat) (h : a.length = b.length) :
    (addCarry a b c).1.length = a.length ∧
    ∀ d ∈ (addCarry a b c).1, d < radix := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil => simp [addCarry]
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      have ht : xs.length = ys.length := Nat.succ.inj h
      have hr := ih ys ((x + y + c) / radix) ht
      simp only [addCarry, List.length_cons, List.mem_cons]
      constructor
      · exact congrArg Nat.succ hr.1
      · intro d hd
        rcases hd with rfl | hd
        · exact Nat.mod_lt _ (by decide : 0 < radix)
        · exact hr.2 d hd

/-- A bounded limb array represents a number strictly below its radix power. -/
theorem assemble_bound (xs : List Nat) (h : ∀ d ∈ xs, d < radix) :
    assemble xs < radix ^ xs.length := by
  induction xs with
  | nil => simp [assemble]
  | cons x rest ih =>
    have hx : x < radix := h x (by simp)
    have ht : ∀ d ∈ rest, d < radix := by
      intro d hd
      exact h d (by simp [hd])
    have hb := ih ht
    simp only [assemble, List.length_cons, Nat.pow_succ]
    dsimp [radix] at hx hb ⊢
    omega

/-- Full wrap equivalence of the emitted limb polynomial, not just one digit. -/
theorem addCarry_wrap (a b : List Nat) (h : a.length = b.length) :
    assemble (addCarry a b 0).1 % radix ^ a.length =
      (assemble a + assemble b) % radix ^ a.length := by
  have hd := addCarry_digits a b 0 h
  have hb := assemble_bound (addCarry a b 0).1 hd.2
  rw [hd.1] at hb
  have he := addCarry_reconstruct a b 0 h
  simp only [Nat.add_zero] at he
  have hm := congrArg (fun z : Nat => z % radix ^ a.length) he
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hb] using hm

/-- Four 16-bit limbs implement 64-bit wrapping addition, with arbitrary
symbolic bounded input limbs and an actual low/carry output. -/
theorem four_limb_add_wrap (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat) :
    assemble (addCarry [a₀, a₁, a₂, a₃] [b₀, b₁, b₂, b₃] 0).1 % 2 ^ 64 =
      (assemble [a₀, a₁, a₂, a₃] + assemble [b₀, b₁, b₂, b₃]) % 2 ^ 64 := by
  simpa [radix, show (65536 : Nat) ^ 4 = 2 ^ 64 by decide] using
    addCarry_wrap [a₀, a₁, a₂, a₃] [b₀, b₁, b₂, b₃] (by rfl)

/-- The same loop used for the 16-bit and 32-bit specializations. -/
theorem one_limb_add_wrap (a₀ b₀ : Nat) :
    assemble (addCarry [a₀] [b₀] 0).1 % 2 ^ 16 =
      (assemble [a₀] + assemble [b₀]) % 2 ^ 16 := by
  simpa [radix, show (65536 : Nat) ^ 1 = 2 ^ 16 by decide] using
    addCarry_wrap [a₀] [b₀] (by rfl)

theorem two_limb_add_wrap (a₀ a₁ b₀ b₁ : Nat) :
    assemble (addCarry [a₀, a₁] [b₀, b₁] 0).1 % 2 ^ 32 =
      (assemble [a₀, a₁] + assemble [b₀, b₁]) % 2 ^ 32 := by
  simpa [radix, show (65536 : Nat) ^ 2 = 2 ^ 32 by decide] using
    addCarry_wrap [a₀, a₁] [b₀, b₁] (by rfl)

#print axioms FixedLimbBridge.digit_carry
#print axioms FixedLimbBridge.addCarry_reconstruct
#print axioms FixedLimbBridge.addCarry_digits
#print axioms FixedLimbBridge.assemble_bound
#print axioms FixedLimbBridge.addCarry_wrap
#print axioms FixedLimbBridge.one_limb_add_wrap
#print axioms FixedLimbBridge.two_limb_add_wrap
#print axioms FixedLimbBridge.four_limb_add_wrap
end FixedLimbBridge
