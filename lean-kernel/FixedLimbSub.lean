import FixedLimbBridge

/-! WRAP subtraction by the actual two addRaw calls: invert every bounded
little-endian limb, add, then add the one-word. This deliberately says nothing
about SATURATE, TRAP, or signed decoding. -/
namespace FixedLimbSub

open FixedLimbBridge

private def base : Nat := 65536

/-- The implementation's limbwise complement, valid only for bounded limbs. -/
def invert (xs : List Nat) : List Nat := xs.map (fun d => base - 1 - d)

/-- The representation of one with precisely as many limbs as a nonempty word. -/
def oneLike : List Nat → List Nat
  | [] => []
  | _ :: xs => 1 :: xs.map (fun _ => 0)

private theorem zero_tail (xs : List Nat) :
    assemble (xs.map (fun _ => 0)) = 0 := by
  induction xs with
  | nil => simp [assemble]
  | cons _ xs ih => simp [assemble, ih, FixedLimbBridge.assemble]

private theorem oneLike_length (xs : List Nat) : (oneLike xs).length = xs.length := by
  cases xs <;> simp [oneLike]

private theorem oneLike_assemble {x : Nat} {xs : List Nat} :
    assemble (oneLike (x :: xs)) = 1 := by
  simp [oneLike, assemble, zero_tail]

/-- Complement is the all-ones word, not a truncated natural subtraction.
The proof works at arbitrary limb count; the fixed sizes below instantiate it. -/
theorem complement (xs : List Nat) (h : ∀ d ∈ xs, d < base) :
    assemble xs + assemble (invert xs) + 1 = base ^ xs.length := by
  induction xs with
  | nil => simp [assemble, invert, base]
  | cons x xs ih =>
    have hx : x < base := h x (by simp)
    have ht : ∀ d ∈ xs, d < base := by
      intro d hd
      exact h d (by simp [hd])
    have hr := ih ht
    simp only [List.length_cons, Nat.pow_succ, invert, List.map_cons, assemble]
    simp only [invert] at hr
    dsimp [base, FixedLimbBridge.radix] at hx hr ⊢
    omega

/-- The exact result of addRaw(a,invert(b)), followed by
addRaw(low,one): subtraction in the residue ring, not Nat subtraction.
The precondition b<M makes (a+M)-b an ordinary Nat representative. -/
theorem subtract_wrap (a b : List Nat)
    (hlen : a.length = b.length) (hne : a ≠ [])
    (hb : ∀ d ∈ b, d < base) :
    let low := (addCarry a (invert b) 0).1
    assemble (addCarry low (oneLike a) 0).1 % base ^ a.length =
      (assemble a + base ^ a.length - assemble b) % base ^ a.length := by
  dsimp
  have hi : (invert b).length = b.length := by simp [invert]
  have hfirst : a.length = (invert b).length := hlen.trans hi.symm
  have hlo := (addCarry_digits a (invert b) 0 hfirst).1
  have hone : assemble (oneLike a) = 1 := by
    cases a with
    | nil => exact False.elim (hne rfl)
    | cons x xs => exact oneLike_assemble
  have hc := complement b hb
  have bound := assemble_bound b (by
    intro d hd
    exact hb d hd)
  have hmod := addCarry_wrap (addCarry a (invert b) 0).1 (oneLike a)
    (hlo.trans (oneLike_length a).symm)
  have hfirstmod := addCarry_wrap a (invert b) hfirst
  rw [hlo] at hmod
  rw [hone] at hmod
  rw [← hlen] at hc
  change assemble b < 65536 ^ b.length at bound
  rw [← hlen] at bound
  dsimp [base] at hc ⊢
  have he : assemble a + assemble (invert b) + 1 =
      assemble a + (65536 ^ a.length - assemble b) := by omega
  have heq : (assemble (addCarry a (invert b) 0).1 + 1) % 65536 ^ a.length =
      (assemble a + assemble (invert b) + 1) % 65536 ^ a.length := by
    change assemble (addCarry a (invert b) 0).1 % 65536 ^ a.length =
      (assemble a + assemble (invert b)) % 65536 ^ a.length at hfirstmod
    simpa only [Nat.add_mod, Nat.mod_mod] using
      congrArg (fun z : Nat => (z + 1) % 65536 ^ a.length) hfirstmod
  calc
    assemble (addCarry (addCarry a (invert b) 0).1 (oneLike a) 0).1 %
        65536 ^ a.length =
        (assemble (addCarry a (invert b) 0).1 + 1) % 65536 ^ a.length := by
          simpa [FixedLimbBridge.radix] using hmod
    _ = (assemble a + assemble (invert b) + 1) % 65536 ^ a.length := heq
    _ = (assemble a + (65536 ^ a.length - assemble b)) % 65536 ^ a.length := by rw [he]
    _ = (assemble a + 65536 ^ a.length - assemble b) % 65536 ^ a.length := by
      congr 1
      omega

/-- Explicit 8-bit static specialization (one radix-256 digit). -/
theorem byte_complement (b : Nat) (hb : b < 256) : b + (255 - b) + 1 = 256 := by
  omega

/-- Explicit 16-, 32-, and 64-bit limb counts; the generic result above
covers every positive count with the same implementation loop. -/
theorem sub16 (a₀ b₀ : Nat) (hb₀ : b₀ < 65536) :
    let a := [a₀]; let b := [b₀]
    assemble (addCarry (addCarry a (invert b) 0).1 (oneLike a) 0).1 % 2 ^ 16 =
      (assemble a + 2 ^ 16 - assemble b) % 2 ^ 16 := by
  simpa [base, show (65536 : Nat) ^ 1 = 2 ^ 16 by decide] using
    subtract_wrap [a₀] [b₀] (by simp) (by simp) (by simpa [base] using hb₀)

theorem sub32 (a₀ a₁ b₀ b₁ : Nat) (hb₀ : b₀ < 65536) (hb₁ : b₁ < 65536) :
    let a := [a₀, a₁]; let b := [b₀, b₁]
    assemble (addCarry (addCarry a (invert b) 0).1 (oneLike a) 0).1 % 2 ^ 32 =
      (assemble a + 2 ^ 32 - assemble b) % 2 ^ 32 := by
  simpa [base, show (65536 : Nat) ^ 2 = 2 ^ 32 by decide] using
    subtract_wrap [a₀, a₁] [b₀, b₁] (by simp) (by simp)
      (by simpa [base] using (show b₀ < 65536 ∧ b₁ < 65536 from ⟨hb₀, hb₁⟩))

theorem sub64 (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat)
    (hb₀ : b₀ < 65536) (hb₁ : b₁ < 65536)
    (hb₂ : b₂ < 65536) (hb₃ : b₃ < 65536) :
    let a := [a₀, a₁, a₂, a₃]; let b := [b₀, b₁, b₂, b₃]
    assemble (addCarry (addCarry a (invert b) 0).1 (oneLike a) 0).1 % 2 ^ 64 =
      (assemble a + 2 ^ 64 - assemble b) % 2 ^ 64 := by
  simpa [base, show (65536 : Nat) ^ 4 = 2 ^ 64 by decide] using
    subtract_wrap [a₀, a₁, a₂, a₃] [b₀, b₁, b₂, b₃] (by simp) (by simp)
      (by simpa [base] using
        (show b₀ < 65536 ∧ b₁ < 65536 ∧ b₂ < 65536 ∧ b₃ < 65536 from
          ⟨hb₀, hb₁, hb₂, hb₃⟩))

end FixedLimbSub
