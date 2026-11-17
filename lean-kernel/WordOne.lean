import WordLex

/-! Divisor-one digits for the normalized little-endian source operand. No
schema-generated fact is a premise of this numeric theorem. -/
namespace WordOne

/-- Extraction is inverse to assembly for a bounded little-endian word. -/
theorem digit_assemble (base : Nat) (xs : List Nat) (hb : 0 < base)
    (hxs : ∀ x ∈ xs, x < base) (i : Nat) (hi : i < xs.length) :
    WordDivision.digit base (WordDivision.assemble base xs) i = xs[i]?.getD 0 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      have hx : x < base := hxs x (by simp)
      have ht : ∀ y ∈ xs, y < base := by
        intro y hy
        exact hxs y (by simp [hy])
      cases i with
      | zero =>
          simp [WordDivision.digit, WordDivision.assemble, Nat.mod_eq_of_lt hx]
      | succ i =>
          have hs (z : Nat) : WordDivision.digit base z (i+1) =
              WordDivision.digit base (z/base) i := by
            unfold WordDivision.digit
            rw [Nat.pow_succ, Nat.mul_comm (base^i) base, ← Nat.div_div_eq_div_mul]
          rw [hs]
          have hdiv : WordDivision.assemble base (x::xs) / base =
              WordDivision.assemble base xs := by
            simp [WordDivision.assemble, Nat.add_mul_div_left, Nat.div_eq_of_lt hx, hb]
          rw [hdiv]
          simpa using ih ht i (by simpa using hi)

/-- The source operand's reconstructed digit is its original normalized limb. -/
theorem input_digit (w : Nat) (v : List Nat)
    (hlen : WordDivision.limbs w ≤ v.length) (i : Nat) (hi : i < WordDivision.limbs w) :
    WordDivision.digit (WordDivision.radix w) (WordDivision.wordA w v) i =
      WordDivision.inputDigit w v i := by
  let ds := (List.range (WordDivision.limbs w)).map (WordDivision.inputDigit w v)
  have hds : ∀ x ∈ ds, x < WordDivision.radix w := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact Nat.mod_lt _ (WordDivision.radix_pos w)
  have h := digit_assemble (WordDivision.radix w) ds (WordDivision.radix_pos w) hds i (by simpa [ds] using hi)
  rw [WordLex.assemble_inputDigits w v hlen] at h
  simpa [ds, hi] using h

/-- With divisor one, every quotient limb is exactly its input limb and every
remainder limb is zero, at all four supported widths and all natural inputs. -/
theorem divisor_one_digits (w : Nat) (v : List Nat)
    (_hw : w ∈ [8,16,32,64]) (hlen : v.length = 2*WordDivision.limbs w)
    (hb : WordDivision.wordB w v = 1) :
    ∀ i < WordDivision.limbs w,
      WordDivision.qDigit w v i = WordDivision.inputDigit w v i ∧
      WordDivision.rDigit w v i = 0 := by
  intro i hi
  obtain ⟨hq, hr⟩ := WordDivision.divisor_one_digits w v hb i
  exact ⟨hq.trans (input_digit w v (by omega) i hi), hr⟩

/-- The generator's divisor-one digit shape really denotes numeric one. -/
theorem b_digits_one (w : Nat) (v : List Nat)
    (hw : w ∈ [8,16,32,64]) (hlen : v.length = 2*WordDivision.limbs w)
    (h0 : WordDivision.bDigit w v 0 = 1)
    (hrest : ∀ i, 1 ≤ i → i < WordDivision.limbs w → WordDivision.bDigit w v i = 0) :
    WordDivision.wordB w v = 1 := by
  rw [← WordLex.assemble_bDigits w v (by omega)]
  have hn : WordDivision.limbs w = 1 ∨ WordDivision.limbs w = 2 ∨ WordDivision.limbs w = 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> simp [WordDivision.limbs]
  rcases hn with hn | hn | hn
  · simp [hn, List.range_succ, WordDivision.assemble, h0]
  · have h1 := hrest 1 (by decide) (by omega)
    simp [hn, List.range_succ, WordDivision.assemble, h0, h1]
  · have h1 := hrest 1 (by decide) (by omega)
    have h2 := hrest 2 (by decide) (by omega)
    have h3 := hrest 3 (by decide) (by omega)
    simp [hn, List.range_succ, WordDivision.assemble, h0, h1, h2, h3]

end WordOne
#print axioms WordOne.divisor_one_digits
#print axioms WordOne.b_digits_one
