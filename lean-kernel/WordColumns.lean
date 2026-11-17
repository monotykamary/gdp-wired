import WordDivision

/-! Numeric wrapper for the columns emitted by `wordDivisionFacts` in
`kernel/word-division.ts`. Input digits are zero-padded above the dividend's
`n` limbs: `WordDivision.inputDigit` itself reads the full input list, including
its divisor half, so it must only be used below `n` in a column equation.
All input limbs may be arbitrary natural numbers; WordDivision normalizes them.
-/
namespace WordColumns
open WordDivision

private theorem list_two (v : List Nat) (h : v.length = 2) :
    ∃ a b, v = [a, b] := by
  rcases v with _ | ⟨a, _ | ⟨b, v⟩⟩
  · simp at h
  · simp at h
  have hv : v = [] := by simpa using h
  subst v
  exact ⟨a, b, rfl⟩

private theorem list_four (v : List Nat) (h : v.length = 4) :
    ∃ a₀ a₁ b₀ b₁, v = [a₀, a₁, b₀, b₁] := by
  rcases v with _ | ⟨a₀, _ | ⟨a₁, _ | ⟨b₀, _ | ⟨b₁, v⟩⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  have hv : v = [] := by simpa using h
  subst v
  exact ⟨a₀, a₁, b₀, b₁, rfl⟩

private theorem list_eight (v : List Nat) (h : v.length = 8) :
    ∃ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃, v = [a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃] := by
  rcases v with _ | ⟨a₀, _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃,
    _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, v⟩⟩⟩⟩⟩⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  have hv : v = [] := by simpa using h
  subst v
  exact ⟨a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃, rfl⟩

private theorem one_limb (w : Nat) (v : List Nat) (hn : limbs w = 1)
    (hlen : v.length = 2) (hb : wordB w v ≠ 0) :
    (∀ i < 2 * limbs w,
      carry w v i + (if i < limbs w then rDigit w v i else 0) +
        convolution w v i =
      (if i < limbs w then inputDigit w v i else 0) +
        radix w * carry w v (i + 1)) ∧
    carry w v (limbs w) = 0 := by
  obtain ⟨a, b, rfl⟩ := list_two v hlen
  have hb' : b % radix w ≠ 0 := by
    simpa [wordB, normalize, assemble, hn] using hb
  obtain ⟨h₀, h₁⟩ := single_limb_columns w a b hn hb'
  constructor
  · intro i hi
    have his : i = 0 ∨ i = 1 := by rw [hn] at hi; omega
    rcases his with rfl | rfl
    · simpa [hn] using h₀
    · simpa [hn] using h₁
  · simpa [hn] using single_limb_carry_zero w a b hn hb'

/-- All generated low and zero-padded high columns, and the carry at the word
boundary, for every supported width and arbitrary (not necessarily bounded)
natural input limbs. This is the numeric equation used by WordFacts.column. -/
theorem columns_and_carry (w : Nat) (v : List Nat)
    (hw : w ∈ [8, 16, 32, 64])
    (hlen : v.length = 2 * WordDivision.limbs w)
    (hb : WordDivision.wordB w v ≠ 0) :
    (∀ i < 2 * WordDivision.limbs w,
      WordDivision.carry w v i +
        (if i < WordDivision.limbs w then WordDivision.rDigit w v i else 0) +
        WordDivision.convolution w v i =
      (if i < WordDivision.limbs w then WordDivision.inputDigit w v i else 0) +
        WordDivision.radix w * WordDivision.carry w v (i + 1)) ∧
    WordDivision.carry w v (WordDivision.limbs w) = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact one_limb 8 v (by decide) (by simpa [limbs] using hlen) hb
  · exact one_limb 16 v (by decide) (by simpa [limbs] using hlen) hb
  · obtain ⟨a₀, a₁, b₀, b₁, rfl⟩ :=
      list_four v (by simpa [limbs] using hlen)
    constructor
    · intro i hi
      by_cases hlow : i < 2
      · simpa [limbs, radix, hlow] using
          thirty_two_bit_low_columns a₀ a₁ b₀ b₁ hb i hlow
      · have his : i = 2 ∨ i = 3 := by
          have hi' : i < 4 := by simpa [limbs] using hi
          omega
        have hc := thirty_two_bit_high_columns a₀ a₁ b₀ b₁ hb
        rcases his with rfl | rfl
        · simpa [limbs, radix] using hc.1
        · simpa [limbs, radix] using hc.2.1
    · simpa [limbs] using thirty_two_bit_carry_zero a₀ a₁ b₀ b₁ hb
  · obtain ⟨a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃, rfl⟩ :=
      list_eight v (by simpa [limbs] using hlen)
    constructor
    · intro i hi
      by_cases hlow : i < 4
      · simpa [limbs, radix, hlow] using
          sixty_four_bit_columns a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ hb i hlow
      · have hi' : i < 8 := by simpa [limbs] using hi
        simpa [limbs, radix, hlow] using
          sixty_four_bit_high_columns a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ hb i (by omega) hi'
    · simpa [limbs] using
        sixty_four_bit_carry_zero a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ hb

/-- A bounded negative control: the high input digit is a divisor digit, not
padding. Using it unconditionally would falsely require `0 = 1`. -/
theorem unpadded_high_column_counterexample :
    wordB 8 [1, 1] ≠ 0 ∧
    carry 8 [1, 1] 1 + convolution 8 [1, 1] 1 ≠
      inputDigit 8 [1, 1] 1 + radix 8 * carry 8 [1, 1] 2 := by
  decide

#print axioms WordColumns.columns_and_carry
#print axioms WordColumns.unpadded_high_column_counterexample
end WordColumns
