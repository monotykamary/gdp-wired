import WordDivision

/-! Numeric order implies most-significant-differing-digit order for bounded
little-endian words, independently of the number of digits. -/
namespace WordLex

/-- A strict comparison at one digit, with equality at all higher digits. -/
def lt (xs ys : List Nat) : Prop :=
  ∃ i, i < xs.length ∧
    (∀ j, i < j → j < xs.length → xs[j]?.getD 0 = ys[j]?.getD 0) ∧
    xs[i]?.getD 0 < ys[i]?.getD 0

/-- Non-strict little-endian lexicographic order, including word equality. -/
def le (xs ys : List Nat) : Prop := lt xs ys ∨ xs = ys

/-- Bounded equal-length words are ordered by their highest differing digit. -/
theorem assemble_le_to_lt_or_eq (base : Nat) (xs ys : List Nat)
    (hb : 1 < base) (hlen : xs.length = ys.length)
    (hxs : ∀ x ∈ xs, x < base) (hys : ∀ y ∈ ys, y < base)
    (h : WordDivision.assemble base xs ≤ WordDivision.assemble base ys) :
    lt xs ys ∨ xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact Or.inr rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hlen' : xs.length = ys.length := by simpa using hlen
          have hx : x < base := hxs x (by simp)
          have hy : y < base := hys y (by simp)
          have hxs' : ∀ z ∈ xs, z < base := by
            intro z hz
            exact hxs z (by simp [hz])
          have hys' : ∀ z ∈ ys, z < base := by
            intro z hz
            exact hys z (by simp [hz])
          have ht : WordDivision.assemble base xs ≤ WordDivision.assemble base ys := by
            by_cases hn : WordDivision.assemble base xs ≤ WordDivision.assemble base ys
            · exact hn
            have hm := Nat.mul_le_mul_left base
              (show WordDivision.assemble base ys + 1 ≤ WordDivision.assemble base xs by omega)
            simp only [Nat.mul_add, Nat.mul_one] at hm
            simp only [WordDivision.assemble] at h
            omega
          rcases ih ys hlen' hxs' hys' ht with hlt | heq
          · left
            rcases hlt with ⟨i, hi, hh, hl⟩
            refine ⟨i + 1, by simp; omega, ?_, ?_⟩
            · intro j hij hj
              cases j with
              | zero => omega
              | succ j =>
                  simpa using hh j (by omega) (by simpa using hj)
            · simpa using hl
          · have hxy : x ≤ y := by
              simp only [WordDivision.assemble, heq] at h
              omega
            rcases Nat.lt_or_eq_of_le hxy with hlt | he
            · left
              refine ⟨0, by simp, ?_, ?_⟩
              · intro j hj _
                cases j with
                | zero => omega
                | succ j => simp [heq]
              · simpa using hlt
            · right
              simp [he, heq]

/-- Strict numeric order gives a strict lexicographic witness. -/
theorem assemble_lt_to_lt (base : Nat) (xs ys : List Nat)
    (hb : 1 < base) (hlen : xs.length = ys.length)
    (hxs : ∀ x ∈ xs, x < base) (hys : ∀ y ∈ ys, y < base)
    (h : WordDivision.assemble base xs < WordDivision.assemble base ys) :
    lt xs ys := by
  rcases assemble_le_to_lt_or_eq base xs ys hb hlen hxs hys (Nat.le_of_lt h) with hl | he
  · exact hl
  · subst ys
    exact False.elim (Nat.lt_irrefl _ h)

/-- The successive-remainder representation agrees with indexed digits. -/
theorem range_digits (base x n : Nat) :
    (List.range n).map (WordDivision.digit base x) = WordDivision.digits base x n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hs (i : Nat) :
          WordDivision.digit base x (i + 1) = WordDivision.digit base (x / base) i := by
        unfold WordDivision.digit
        rw [Nat.pow_succ, Nat.mul_comm (base ^ i) base, ← Nat.div_div_eq_div_mul]
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map,
        Function.comp_def, WordDivision.digits]
      simp only [hs, ih]
      simp [WordDivision.digit]

/-- Assemble all indexed digits of a number that fits in the word. -/
theorem assemble_range_digits (base x n : Nat) (h : x < base ^ n) :
    WordDivision.assemble base ((List.range n).map (WordDivision.digit base x)) = x := by
  rw [range_digits]
  have he := WordDivision.digits_reconstruct base x n
  simpa [Nat.div_eq_of_lt h] using he

/-- Indexed, zero-defaulted input extraction agrees with a bounded list prefix. -/
theorem range_input_take (base n : Nat) (v : List Nat) (hn : n ≤ v.length) :
    (List.range n).map (fun i => (v[i]?.getD 0) % base) =
      (v.take n).map (fun x => x % base) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      cases v with
      | nil => simp at hn
      | cons x xs =>
          have ht : n ≤ xs.length := by simpa using hn
          simpa [List.range_succ_eq_map, List.map_map, Function.comp_def] using
            congrArg (List.cons (x % base)) (ih xs ht)

/-- The normalized input digit list assembles to operand A. -/
theorem assemble_inputDigits (w : Nat) (v : List Nat)
    (hn : WordDivision.limbs w ≤ v.length) :
    WordDivision.assemble (WordDivision.radix w)
      ((List.range (WordDivision.limbs w)).map (WordDivision.inputDigit w v)) =
        WordDivision.wordA w v := by
  exact congrArg (WordDivision.assemble (WordDivision.radix w))
      (range_input_take (WordDivision.radix w) (WordDivision.limbs w) v hn)

/-- The normalized divisor digit list assembles to operand B. -/
theorem assemble_bDigits (w : Nat) (v : List Nat)
    (hn : 2 * WordDivision.limbs w ≤ v.length) :
    WordDivision.assemble (WordDivision.radix w)
      ((List.range (WordDivision.limbs w)).map (WordDivision.bDigit w v)) =
        WordDivision.wordB w v := by
  have ht : WordDivision.limbs w ≤ (v.drop (WordDivision.limbs w)).length := by
    simp only [List.length_drop]
    omega
  unfold WordDivision.bDigit WordDivision.inputDigit WordDivision.wordB WordDivision.normalize
  simpa only [List.getElem?_drop] using
    congrArg (WordDivision.assemble (WordDivision.radix w))
      (range_input_take (WordDivision.radix w) (WordDivision.limbs w)
        (v.drop (WordDivision.limbs w)) ht)

/-- A positive digit makes the assembled word positive. -/
theorem assemble_pos_of_mem (base : Nat) (xs : List Nat) (hb : 0 < base)
    (z : Nat) (hz : z ∈ xs) (hpos : 0 < z) : 0 < WordDivision.assemble base xs := by
  induction xs with
  | nil => simp at hz
  | cons x xs ih =>
      rcases List.mem_cons.mp hz with he | ht
      · subst x
        simp only [WordDivision.assemble]
        omega
      · have hp := Nat.mul_pos hb (ih ht)
        simp only [WordDivision.assemble]
        omega

/-- A positive normalized divisor digit rules out the zero-divisor branch. -/
theorem wordB_nonzero (w : Nat) (v : List Nat)
    (hw : w ∈ [8,16,32,64]) (hlen : v.length = 2 * WordDivision.limbs w)
    (hpos : ∃ i, i < WordDivision.limbs w ∧ 0 < WordDivision.bDigit w v i) :
    WordDivision.wordB w v ≠ 0 := by
  obtain ⟨i, hi, hp⟩ := hpos
  have hm : WordDivision.bDigit w v i ∈
      (List.range (WordDivision.limbs w)).map (WordDivision.bDigit w v) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have ha := assemble_pos_of_mem (WordDivision.radix w)
    ((List.range (WordDivision.limbs w)).map (WordDivision.bDigit w v))
    (WordDivision.radix_pos w) (WordDivision.bDigit w v i) hm hp
  rw [assemble_bDigits w v (by omega)] at ha
  exact Nat.ne_of_gt ha

/-- Remainder and quotient comparisons in the exact digit lists used by WordFacts. -/
theorem word_lex (w : Nat) (v : List Nat)
    (hw : w ∈ [8,16,32,64]) (hlen : v.length = 2 * WordDivision.limbs w)
    (hb : WordDivision.wordB w v ≠ 0) :
    lt ((List.range (WordDivision.limbs w)).map (WordDivision.rDigit w v))
      ((List.range (WordDivision.limbs w)).map (WordDivision.bDigit w v)) ∧
    (lt ((List.range (WordDivision.limbs w)).map (WordDivision.qDigit w v))
      ((List.range (WordDivision.limbs w)).map (WordDivision.inputDigit w v)) ∨
    (List.range (WordDivision.limbs w)).map (WordDivision.qDigit w v) =
      (List.range (WordDivision.limbs w)).map (WordDivision.inputDigit w v)) := by
  have hn : WordDivision.limbs w ≤ v.length := by omega
  have hbn : WordDivision.limbs w ≤ (v.drop (WordDivision.limbs w)).length := by
    simp only [List.length_drop]
    omega
  have ha : WordDivision.wordA w v < WordDivision.radix w ^ WordDivision.limbs w := by
    simpa [List.length_take, Nat.min_eq_left hn] using WordDivision.wordA_bound w v
  have hbd : WordDivision.wordB w v < WordDivision.radix w ^ WordDivision.limbs w := by
    have hbound := WordDivision.wordB_bound w v
    rw [List.length_take, Nat.min_eq_left hbn] at hbound
    exact hbound
  have hq : WordDivision.quotient w v < WordDivision.radix w ^ WordDivision.limbs w :=
    Nat.lt_of_le_of_lt (WordDivision.quotient_le w v hb) ha
  have hr : WordDivision.remainder w v < WordDivision.radix w ^ WordDivision.limbs w :=
    Nat.lt_trans (WordDivision.remainder_lt w v hb) hbd
  have hqe : WordDivision.assemble (WordDivision.radix w)
      ((List.range (WordDivision.limbs w)).map (WordDivision.qDigit w v)) =
        WordDivision.quotient w v :=
    assemble_range_digits (WordDivision.radix w) (WordDivision.quotient w v)
      (WordDivision.limbs w) hq
  have hre : WordDivision.assemble (WordDivision.radix w)
      ((List.range (WordDivision.limbs w)).map (WordDivision.rDigit w v)) =
        WordDivision.remainder w v :=
    assemble_range_digits (WordDivision.radix w) (WordDivision.remainder w v)
      (WordDivision.limbs w) hr
  constructor
  · apply assemble_lt_to_lt (WordDivision.radix w)
    · exact WordDivision.radix_gt_one w
    · simp
    · intro d hd
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
      exact WordDivision.rDigit_lt w v i
    · intro d hd
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
      exact Nat.mod_lt _ (WordDivision.radix_pos w)
    · rw [hre, assemble_bDigits w v (by omega)]
      exact WordDivision.remainder_lt w v hb
  · apply assemble_le_to_lt_or_eq (WordDivision.radix w)
    · exact WordDivision.radix_gt_one w
    · simp
    · intro d hd
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
      exact WordDivision.qDigit_lt w v i
    · intro d hd
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
      exact Nat.mod_lt _ (WordDivision.radix_pos w)
    · rw [hqe, assemble_inputDigits w v hn]
      exact WordDivision.quotient_le w v hb

end WordLex

#print axioms WordLex.assemble_lt_to_lt
#print axioms WordLex.assemble_le_to_lt_or_eq
#print axioms WordLex.word_lex
#print axioms WordLex.wordB_nonzero
