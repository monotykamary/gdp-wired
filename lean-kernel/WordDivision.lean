import Std

/-! Exact unsigned natural-number semantics of kernel/word-division.ts. Each input
limb is reduced modulo the radix before assembly; division by zero is explicitly
mapped to zero, rather than relying on Lean's total division convention. -/
namespace WordDivision

def radix (width : Nat) : Nat := if width = 8 then 256 else 65536
def limbs (width : Nat) : Nat := if width = 8 then 1 else width / 16

def normalize (base : Nat) (xs : List Nat) : List Nat := xs.map (· % base)

def assemble (base : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x + base * assemble base xs

def digit (base x i : Nat) : Nat := x / base ^ i % base

def wordA (width : Nat) (values : List Nat) : Nat :=
  assemble (radix width) (normalize (radix width) (values.take (limbs width)))
def wordB (width : Nat) (values : List Nat) : Nat :=
  assemble (radix width) (normalize (radix width)
    ((values.drop (limbs width)).take (limbs width)))
def quotient (width : Nat) (values : List Nat) : Nat :=
  if wordB width values = 0 then 0 else wordA width values / wordB width values
def remainder (width : Nat) (values : List Nat) : Nat :=
  if wordB width values = 0 then 0 else wordA width values % wordB width values

def qDigit (width : Nat) (values : List Nat) (i : Nat) : Nat :=
  digit (radix width) (quotient width values) i
def rDigit (width : Nat) (values : List Nat) (i : Nat) : Nat :=
  digit (radix width) (remainder width values) i

theorem radix_pos (w : Nat) : 0 < radix w := by
  unfold radix
  split <;> omega

theorem radix_gt_one (w : Nat) : 1 < radix w := by
  unfold radix
  split <;> omega

theorem digit_lt (w x i : Nat) : digit (radix w) x i < radix w := by
  exact Nat.mod_lt _ (radix_pos w)

theorem qDigit_lt (w : Nat) (v : List Nat) (i : Nat) :
    qDigit w v i < radix w := digit_lt w _ _
theorem rDigit_lt (w : Nat) (v : List Nat) (i : Nat) :
    rDigit w v i < radix w := digit_lt w _ _

/-- The actual successive low-to-high remainder extraction. -/
def digits (base x : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => x % base :: digits base (x / base) n

theorem digits_length (base x n : Nat) : (digits base x n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [digits, ih]

theorem digits_reconstruct (base x n : Nat) :
    assemble base (digits base x n) + base ^ n * (x / base ^ n) = x := by
  induction n generalizing x with
  | zero => simp [digits, assemble]
  | succ n ih =>
    have h := ih (x / base)
    have hd := Nat.mod_add_div x base
    simp only [digits, assemble, Nat.pow_succ]
    -- The recursive quotient divides first by the radix, then by its power.
    simp only [Nat.mul_comm (base ^ n) base]
    rw [← Nat.div_div_eq_div_mul x base (base ^ n)]
    calc
      x % base + base * assemble base (digits base (x / base) n) +
          (base * base ^ n) * ((x / base) / base ^ n) =
        x % base + base * (assemble base (digits base (x / base) n) +
          base ^ n * ((x / base) / base ^ n)) := by
            simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
      _ = x % base + base * (x / base) := by rw [h]
      _ = x := hd

theorem zero_divisor (w : Nat) (v : List Nat) (h : wordB w v = 0) :
    quotient w v = 0 ∧ remainder w v = 0 := by
  simp [quotient, remainder, h]

theorem zero_divisor_digits (w : Nat) (v : List Nat)
    (h : wordB w v = 0) (i : Nat) :
    qDigit w v i = 0 ∧ rDigit w v i = 0 := by
  have ⟨hq, hr⟩ := zero_divisor w v h
  simp [qDigit, rDigit, digit, hq, hr]

theorem division_identity (w : Nat) (v : List Nat)
    (h : wordB w v ≠ 0) :
    wordB w v * quotient w v + remainder w v = wordA w v := by
  simp only [quotient, remainder, if_neg h]
  exact Nat.div_add_mod (wordA w v) (wordB w v)

theorem remainder_lt (w : Nat) (v : List Nat)
    (h : wordB w v ≠ 0) : remainder w v < wordB w v := by
  simp only [remainder, if_neg h]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

theorem quotient_le (w : Nat) (v : List Nat)
    (h : wordB w v ≠ 0) : quotient w v ≤ wordA w v := by
  simp only [quotient, if_neg h]
  exact Nat.div_le_self _ _

theorem divisor_one (w : Nat) (v : List Nat)
    (h : wordB w v = 1) :
    quotient w v = wordA w v ∧ remainder w v = 0 := by
  simp [quotient, remainder, h, Nat.mod_one]

theorem divisor_one_digits (w : Nat) (v : List Nat)
    (h : wordB w v = 1) (i : Nat) :
    qDigit w v i = digit (radix w) (wordA w v) i ∧ rDigit w v i = 0 := by
  have ⟨hq, hr⟩ := divisor_one w v h
  simp [qDigit, rDigit, digit, hq, hr]


/-- The normalized input operand's digit (zero for an absent slot). -/
def inputDigit (width : Nat) (values : List Nat) (i : Nat) : Nat :=
  (values[i]?.getD 0) % radix width

def bDigit (width : Nat) (values : List Nat) (i : Nat) : Nat :=
  inputDigit width values (limbs width + i)

/-- The convolution summands of column col in q*b, exactly as in the TS loop. -/
def convolution (width : Nat) (values : List Nat) (col : Nat) : Nat :=
  ((List.range (limbs width)).map fun j =>
    if j ≤ col ∧ col - j < limbs width then
      qDigit width values j * bDigit width values (col - j) else 0).sum

/-- Iterated quotient-carry of the low-to-high convolution. -/
def carry (width : Nat) (values : List Nat) : Nat → Nat
  | 0 => 0
  | col + 1 =>
    (carry width values col +
      (if col < limbs width then rDigit width values col else 0) +
      convolution width values col) / radix width

/-- The compiler-facing total helper: 'q' and 'r' have slots 0..n-1;
'c' has slots 1..2n. This agrees with wordDivisionValue on valid arguments. -/
def value (width part index : Nat) (values : List Nat) : Nat :=
  if part = 0 then qDigit width values index
  else if part = 1 then rDigit width values index
  else if part = 2 then carry width values index
  else 0

theorem value_q (w i : Nat) (v : List Nat) : value w 0 i v = qDigit w v i := by
  simp [value]
theorem value_r (w i : Nat) (v : List Nat) : value w 1 i v = rDigit w v i := by
  simp [value]
theorem value_c (w i : Nat) (v : List Nat) : value w 2 i v = carry w v i := by
  simp [value]

/-- Unconditional digit bounds, including zero-divisor and out-of-range cases. -/
theorem value_q_lt (w i : Nat) (v : List Nat) : value w 0 i v < radix w := by
  simpa [value_q] using qDigit_lt w v i
theorem value_r_lt (w i : Nat) (v : List Nat) : value w 1 i v < radix w := by
  simpa [value_r] using rDigit_lt w v i


/-- A little-endian array of bounded digits fits in its radix power. -/
theorem assemble_bound (base : Nat) (xs : List Nat) (hp : 0 < base)
    (h : ∀ x ∈ xs, x < base) : assemble base xs < base ^ xs.length := by
  induction xs with
  | nil => simp [assemble]
  | cons x xs ih =>
    have hx : x < base := h x (by simp)
    have ht : ∀ y ∈ xs, y < base := by
      intro y hy
      exact h y (by simp [hy])
    have hs := ih ht
    have hm := Nat.mul_le_mul_left base (Nat.succ_le_of_lt hs)
    simp only [Nat.mul_succ] at hm
    simp only [assemble, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm (base ^ xs.length) base]
    omega

theorem normalize_mem_lt (base : Nat) (xs : List Nat) (hp : 0 < base) :
    ∀ x ∈ normalize base xs, x < base := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact Nat.mod_lt _ hp

theorem wordA_bound (w : Nat) (v : List Nat) :
    wordA w v < radix w ^ (v.take (limbs w)).length := by
  unfold wordA
  simpa [normalize] using assemble_bound (radix w)
    (normalize (radix w) (v.take (limbs w))) (radix_pos w)
    (normalize_mem_lt (radix w) _ (radix_pos w))

theorem wordB_bound (w : Nat) (v : List Nat) :
    wordB w v < radix w ^ ((v.drop (limbs w)).take (limbs w)).length := by
  unfold wordB
  simpa [normalize] using assemble_bound (radix w)
    (normalize (radix w) ((v.drop (limbs w)).take (limbs w))) (radix_pos w)
    (normalize_mem_lt (radix w) _ (radix_pos w))

/-- Each carry is precisely the quotient produced at its column. -/
theorem carry_step (w : Nat) (v : List Nat) (i : Nat) :
    carry w v i + (if i < limbs w then rDigit w v i else 0) +
      convolution w v i =
    radix w * carry w v (i + 1) +
      (carry w v i + (if i < limbs w then rDigit w v i else 0) +
        convolution w v i) % radix w := by
  simpa [carry, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.mod_add_div
    (carry w v i + (if i < limbs w then rDigit w v i else 0) +
      convolution w v i) (radix w)).symm

/-- The emitted carry starts at zero and is nonnegative by its Nat codomain. -/
theorem carry_zero (w : Nat) (v : List Nat) : carry w v 0 = 0 := rfl


/-- The first column already exhausts a one-limb quotient/product. This holds
for all natural limb inputs, not just enumerated samples. -/
theorem single_limb_carry_zero (w a b : Nat) (hn : limbs w = 1)
    (hb : b % radix w ≠ 0) : carry w [a, b] 1 = 0 := by
  have ha : wordA w [a, b] = a % radix w := by
    simp [wordA, normalize, assemble, hn]
  have hbd : wordB w [a, b] = b % radix w := by
    simp [wordB, normalize, assemble, hn]
  have hne : wordB w [a, b] ≠ 0 := by simpa [hbd] using hb
  have hid := division_identity w [a, b] hne
  have hq := quotient_le w [a, b] hne
  have hr := remainder_lt w [a, b] hne
  have hqa : quotient w [a, b] < radix w := by
    have h := Nat.mod_lt a (radix_pos w)
    omega
  have hra : remainder w [a, b] < radix w := by
    have h := Nat.mod_lt b (radix_pos w)
    omega
  have hq0 : qDigit w [a, b] 0 = quotient w [a, b] := by
    simp [qDigit, digit, Nat.mod_eq_of_lt hqa]
  have hr0 : rDigit w [a, b] 0 = remainder w [a, b] := by
    simp [rDigit, digit, Nat.mod_eq_of_lt hra]
  have hc : convolution w [a, b] 0 = quotient w [a, b] * (b % radix w) := by
    simp [convolution, hn, hq0, bDigit, inputDigit]
  have hsmall : remainder w [a, b] +
      quotient w [a, b] * (b % radix w) < radix w := by
    have h := Nat.mod_lt a (radix_pos w)
    have hid' : quotient w [a, b] * (b % radix w) + remainder w [a, b] =
        a % radix w := by simpa [ha, hbd, Nat.mul_comm] using hid
    omega
  simp [carry, hn, hr0, hc, Nat.div_eq_of_lt hsmall]

theorem eight_bit_carry_zero (a b : Nat) (hb : b % 256 ≠ 0) :
    carry 8 [a, b] 1 = 0 := by
  exact single_limb_carry_zero 8 a b (by decide) (by simpa [radix] using hb)

theorem sixteen_bit_carry_zero (a b : Nat) (hb : b % 65536 ≠ 0) :
    carry 16 [a, b] 1 = 0 := by
  exact single_limb_carry_zero 16 a b (by decide) (by simpa [radix] using hb)


/-- Two-column carry elimination is purely algebraic and independent of
particular limb values: the full product fits in two columns. -/
theorem two_column_carry_core (base q₀ q₁ r₀ r₁ b₀ b₁ a₀ a₁ : Nat)
    (hp : 0 < base) (ha₀ : a₀ < base) (ha₁ : a₁ < base)
    (he : (q₀ + base*q₁) * (b₀ + base*b₁) + (r₀ + base*r₁) =
      a₀ + base*a₁) :
    ((r₀ + q₀*b₀) / base + r₁ + q₀*b₁ + q₁*b₀) / base = 0 := by
  have hd := Nat.mod_add_div (r₀ + q₀*b₀) base
  have hring : (q₀ + base*q₁) * (b₀ + base*b₁) + (r₀ + base*r₁) =
      (r₀ + q₀*b₀) + base*(r₁ + q₀*b₁ + q₁*b₀) + base^2*(q₁*b₁) := by
    simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hpoly : (r₀ + q₀*b₀) % base +
      base * ((r₀ + q₀*b₀) / base + r₁ + q₀*b₁ + q₁*b₀) +
      base ^ 2 * (q₁*b₁) = a₀ + base*a₁ := by
    have hexpand := hring.symm.trans he
    simp only [Nat.mul_add] at hexpand ⊢
    omega
  have hsmall : a₀ + base*a₁ < base ^ 2 := by
    have hm := Nat.mul_le_mul_left base (Nat.succ_le_of_lt ha₁)
    simp only [Nat.mul_succ] at hm
    have hh : base ^ 2 = base * base := by simp [Nat.pow_succ, Nat.mul_assoc]
    omega
  have hmult : base * ((r₀ + q₀*b₀) / base + r₁ + q₀*b₁ + q₁*b₀) <
      base * base := by
    have hh : base ^ 2 = base * base := by simp [Nat.pow_succ, Nat.mul_assoc]
    omega
  have hlt : (r₀ + q₀*b₀) / base + r₁ + q₀*b₁ + q₁*b₀ < base := by
    exact Nat.lt_of_mul_lt_mul_left hmult
  exact Nat.div_eq_of_lt hlt


/-- Reconstruct a number below two radix places from its low digits. -/
theorem two_digit_expand (base x : Nat) (h : x < base ^ 2) :
    x = x % base + base * (x / base % base) := by
  have hd := digits_reconstruct base x 2
  have hz : x / base ^ 2 = 0 := Nat.div_eq_of_lt h
  simpa [digits, assemble, hz] using hd.symm

/-- The concrete 32-bit helper's carry after the two low columns is zero. -/
theorem thirty_two_bit_carry_zero (a₀ a₁ b₀ b₁ : Nat)
    (hb : wordB 32 [a₀, a₁, b₀, b₁] ≠ 0) :
    carry 32 [a₀, a₁, b₀, b₁] 2 = 0 := by
  let v := [a₀, a₁, b₀, b₁]
  have ha : wordA 32 v = a₀ % 65536 + 65536 * (a₁ % 65536) := by
    simp [v, wordA, normalize, assemble, radix, limbs]
  have hbd : wordB 32 v = b₀ % 65536 + 65536 * (b₁ % 65536) := by
    simp [v, wordB, normalize, assemble, radix, limbs]
  have habound : wordA 32 v < 65536 ^ 2 := by
    simpa [v, radix, limbs] using wordA_bound 32 v
  have hbbound : wordB 32 v < 65536 ^ 2 := by
    simpa [v, radix, limbs] using wordB_bound 32 v
  have hq : quotient 32 v < 65536 ^ 2 :=
    Nat.lt_of_le_of_lt (quotient_le 32 v hb) habound
  have hr : remainder 32 v < 65536 ^ 2 :=
    Nat.lt_trans (remainder_lt 32 v hb) hbbound
  have hqe := two_digit_expand 65536 (quotient 32 v) hq
  have hre := two_digit_expand 65536 (remainder 32 v) hr
  have he : (qDigit 32 v 0 + 65536*qDigit 32 v 1) *
      (b₀ % 65536 + 65536*(b₁ % 65536)) +
      (rDigit 32 v 0 + 65536*rDigit 32 v 1) =
      a₀ % 65536 + 65536*(a₁ % 65536) := by
    have hqeq : qDigit 32 v 0 + 65536*qDigit 32 v 1 = quotient 32 v := by
      simpa [qDigit, digit, radix] using hqe.symm
    have hreq : rDigit 32 v 0 + 65536*rDigit 32 v 1 = remainder 32 v := by
      simpa [rDigit, digit, radix] using hre.symm
    rw [hqeq, hreq, ← hbd, ← ha]
    simpa [Nat.mul_comm] using division_identity 32 v hb
  have hc : carry 32 v 2 =
      ((rDigit 32 v 0 + qDigit 32 v 0 * (b₀ % 65536)) / 65536 +
        rDigit 32 v 1 + qDigit 32 v 0 * (b₁ % 65536) +
        qDigit 32 v 1 * (b₀ % 65536)) / 65536 := by
    have hrange : List.range 2 = [0, 1] := by decide
    simp [carry, convolution, hrange, bDigit, inputDigit, v, limbs, radix,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  rw [hc]
  exact two_column_carry_core 65536 (qDigit 32 v 0) (qDigit 32 v 1)
    (rDigit 32 v 0) (rDigit 32 v 1) (b₀ % 65536) (b₁ % 65536)
    (a₀ % 65536) (a₁ % 65536) (by decide)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) he


/-- The four-column carry equation over the actual 16-bit radix. -/
theorem four_column_carry_reconstruct (t₀ t₁ t₂ t₃ : Nat) :
    let c₁ := t₀ / 65536
    let c₂ := (c₁ + t₁) / 65536
    let c₃ := (c₂ + t₂) / 65536
    let c₄ := (c₃ + t₃) / 65536
    t₀ % 65536 + 65536 * ((c₁ + t₁) % 65536) +
      65536 ^ 2 * ((c₂ + t₂) % 65536) +
      65536 ^ 3 * ((c₃ + t₃) % 65536) +
      65536 ^ 4 * c₄ =
      t₀ + 65536*t₁ + 65536^2*t₂ + 65536^3*t₃ := by
  dsimp
  have h₀ := Nat.mod_add_div t₀ 65536
  have h₁ := Nat.mod_add_div (t₀ / 65536 + t₁) 65536
  have h₂ := Nat.mod_add_div ((t₀ / 65536 + t₁) / 65536 + t₂) 65536
  have h₃ := Nat.mod_add_div
    (((t₀ / 65536 + t₁) / 65536 + t₂) / 65536 + t₃) 65536
  omega

/-- Exact four-limb polynomial expansion: every high diagonal is retained. -/
theorem four_column_product (q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃
    b₀ b₁ b₂ b₃ : Nat) :
    assemble 65536 [q₀,q₁,q₂,q₃] * assemble 65536 [b₀,b₁,b₂,b₃] +
      assemble 65536 [r₀,r₁,r₂,r₃] =
    (r₀ + q₀*b₀) +
      65536*(r₁ + q₀*b₁+q₁*b₀) +
      65536^2*(r₂ + q₀*b₂+q₁*b₁+q₂*b₀) +
      65536^3*(r₃ + q₀*b₃+q₁*b₂+q₂*b₁+q₃*b₀) +
      65536^4*(q₁*b₃+q₂*b₂+q₃*b₁ +
        65536*(q₂*b₃+q₃*b₂) + 65536^2*(q₃*b₃)) := by
  simp [assemble, Nat.pow_succ, Nat.mul_add, Nat.add_mul,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- No carry escapes the fourth low column when the whole unsigned product
and remainder equal a four-limb word. Universal in all twelve digits. -/
theorem four_column_carry_core (q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃
    b₀ b₁ b₂ b₃ a₀ a₁ a₂ a₃ : Nat)
    (ha₀ : a₀ < 65536) (ha₁ : a₁ < 65536)
    (ha₂ : a₂ < 65536) (ha₃ : a₃ < 65536)
    (he : assemble 65536 [q₀,q₁,q₂,q₃] *
        assemble 65536 [b₀,b₁,b₂,b₃] + assemble 65536 [r₀,r₁,r₂,r₃] =
      assemble 65536 [a₀,a₁,a₂,a₃]) :
    let t₀ := r₀ + q₀*b₀
    let t₁ := r₁ + q₀*b₁+q₁*b₀
    let t₂ := r₂ + q₀*b₂+q₁*b₁+q₂*b₀
    let t₃ := r₃ + q₀*b₃+q₁*b₂+q₂*b₁+q₃*b₀
    ((((t₀ / 65536 + t₁) / 65536 + t₂) / 65536 + t₃) / 65536) = 0 := by
  dsimp only
  have hc := four_column_carry_reconstruct (r₀ + q₀*b₀)
    (r₁ + q₀*b₁+q₁*b₀) (r₂ + q₀*b₂+q₁*b₁+q₂*b₀)
    (r₃ + q₀*b₃+q₁*b₂+q₂*b₁+q₃*b₀)
  dsimp only at hc
  have hp := four_column_product q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ b₀ b₁ b₂ b₃
  have hb : assemble 65536 [a₀,a₁,a₂,a₃] < 65536 ^ 4 := by
    apply assemble_bound 65536 [a₀,a₁,a₂,a₃] (by decide)
    intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    all_goals assumption
  rw [he] at hp
  omega


/-- Four successive quotients/remainders recover the bounded word. -/
theorem four_digit_expand (base x : Nat) (h : x < base ^ 4) :
    x = assemble base [digit base x 0, digit base x 1,
      digit base x 2, digit base x 3] := by
  have hd := digits_reconstruct base x 4
  have hz : x / base ^ 4 = 0 := Nat.div_eq_of_lt h
  rw [hz] at hd
  simp only [Nat.mul_zero, Nat.add_zero] at hd
  simpa [digits, assemble, digit, Nat.div_div_eq_div_mul,
    Nat.pow_succ, Nat.mul_assoc] using hd.symm

set_option maxHeartbeats 2000000
/-- Full 64-bit division helper: the carry after four low columns vanishes for
all eight input limbs, after normalization, whenever the divisor is nonzero. -/
theorem sixty_four_bit_carry_zero (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat)
    (hb : wordB 64 [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃] ≠ 0) :
    carry 64 [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃] 4 = 0 := by
  let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
  have ha : wordA 64 v = assemble 65536
      [a₀%65536,a₁%65536,a₂%65536,a₃%65536] := by
    simp [v, wordA, normalize, radix, limbs]
  have hbd : wordB 64 v = assemble 65536
      [b₀%65536,b₁%65536,b₂%65536,b₃%65536] := by
    simp [v, wordB, normalize, radix, limbs]
  have habound : wordA 64 v < 65536 ^ 4 := by
    simpa [v, radix, limbs] using wordA_bound 64 v
  have hbbound : wordB 64 v < 65536 ^ 4 := by
    simpa [v, radix, limbs] using wordB_bound 64 v
  have hq : quotient 64 v < 65536 ^ 4 :=
    Nat.lt_of_le_of_lt (quotient_le 64 v hb) habound
  have hr : remainder 64 v < 65536 ^ 4 :=
    Nat.lt_trans (remainder_lt 64 v hb) hbbound
  have hqe := four_digit_expand 65536 (quotient 64 v) hq
  have hre := four_digit_expand 65536 (remainder 64 v) hr
  have he : assemble 65536 [qDigit 64 v 0,qDigit 64 v 1,
      qDigit 64 v 2,qDigit 64 v 3] *
      assemble 65536 [b₀%65536,b₁%65536,b₂%65536,b₃%65536] +
      assemble 65536 [rDigit 64 v 0,rDigit 64 v 1,
        rDigit 64 v 2,rDigit 64 v 3] =
      assemble 65536 [a₀%65536,a₁%65536,a₂%65536,a₃%65536] := by
    have hqeq : assemble 65536 [qDigit 64 v 0,qDigit 64 v 1,
        qDigit 64 v 2,qDigit 64 v 3] = quotient 64 v := by
      simpa [qDigit, radix] using hqe.symm
    have hreq : assemble 65536 [rDigit 64 v 0,rDigit 64 v 1,
        rDigit 64 v 2,rDigit 64 v 3] = remainder 64 v := by
      simpa [rDigit, radix] using hre.symm
    rw [hqeq, hreq, ← hbd, ← ha]
    simpa [Nat.mul_comm] using division_identity 64 v hb
  have hc : carry 64 v 4 =
      let t₀ := rDigit 64 v 0 + qDigit 64 v 0*(b₀%65536)
      let t₁ := rDigit 64 v 1 + qDigit 64 v 0*(b₁%65536) + qDigit 64 v 1*(b₀%65536)
      let t₂ := rDigit 64 v 2 + qDigit 64 v 0*(b₂%65536) + qDigit 64 v 1*(b₁%65536) + qDigit 64 v 2*(b₀%65536)
      let t₃ := rDigit 64 v 3 + qDigit 64 v 0*(b₃%65536) + qDigit 64 v 1*(b₂%65536) + qDigit 64 v 2*(b₁%65536) + qDigit 64 v 3*(b₀%65536)
      ((((t₀ / 65536 + t₁) / 65536 + t₂) / 65536 + t₃) / 65536) := by
    have hrange : List.range 4 = [0,1,2,3] := by decide
    simp [carry, convolution, hrange, bDigit, inputDigit, v, limbs, radix]
    omega
  rw [hc]
  exact four_column_carry_core (qDigit 64 v 0) (qDigit 64 v 1)
    (qDigit 64 v 2) (qDigit 64 v 3) (rDigit 64 v 0) (rDigit 64 v 1)
    (rDigit 64 v 2) (rDigit 64 v 3) (b₀%65536) (b₁%65536)
    (b₂%65536) (b₃%65536) (a₀%65536) (a₁%65536)
    (a₂%65536) (a₃%65536)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) he


/-- Division by zero is zero throughout every carry column as well as both
quotient/remainder digit arrays. -/
theorem zero_divisor_carry (w : Nat) (v : List Nat)
    (h : wordB w v = 0) (i : Nat) : carry w v i = 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hr := (zero_divisor_digits w v h i).2
    have hc : convolution w v i = 0 := by
      simp only [convolution, qDigit, digit, quotient, h]
      have hz : ∀ xs : List Nat, (xs.map fun _ => (0 : Nat)).sum = 0 := by
        intro xs
        induction xs with
        | nil => rfl
        | cons x xs ih => simp [ih]
      simpa using hz (List.range (limbs w))
    simp [carry, ih, hr, hc]

/-- Zero divisor also gives zero for all three observable parts, even outside
nominal index ranges; it does not depend on caller-supplied digit bounds. -/
theorem zero_divisor_value (w i : Nat) (v : List Nat)
    (h : wordB w v = 0) :
    value w 0 i v = 0 ∧ value w 1 i v = 0 ∧ value w 2 i v = 0 := by
  simp [value_q, value_r, value_c, (zero_divisor_digits w v h i).1,
    (zero_divisor_digits w v h i).2, zero_divisor_carry w v h i]


set_option maxHeartbeats 2000000
/-- All four low-column equations follow from the exact full product, not from
an assumed carry invariant. The emitted digits are unique bounded radix digits. -/
private theorem four_column_eq_core (q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃
    b₀ b₁ b₂ b₃ a₀ a₁ a₂ a₃ : Nat)
    (ha₀ : a₀ < 65536) (ha₁ : a₁ < 65536)
    (ha₂ : a₂ < 65536) (ha₃ : a₃ < 65536)
    (he : assemble 65536 [q₀,q₁,q₂,q₃] *
      assemble 65536 [b₀,b₁,b₂,b₃] + assemble 65536 [r₀,r₁,r₂,r₃] =
      assemble 65536 [a₀,a₁,a₂,a₃]) :
    let t₀ := r₀ + q₀*b₀
    let t₁ := r₁ + q₀*b₁+q₁*b₀
    let t₂ := r₂ + q₀*b₂+q₁*b₁+q₂*b₀
    let t₃ := r₃ + q₀*b₃+q₁*b₂+q₂*b₁+q₃*b₀
    let c₁ := t₀ / 65536
    let c₂ := (c₁+t₁) / 65536
    let c₃ := (c₂+t₂) / 65536
    let c₄ := (c₃+t₃) / 65536
    t₀ = a₀ + 65536*c₁ ∧
    c₁+t₁ = a₁ + 65536*c₂ ∧
    c₂+t₂ = a₂ + 65536*c₃ ∧
    c₃+t₃ = a₃ + 65536*c₄ := by
  dsimp only
  have hc := four_column_carry_reconstruct (r₀ + q₀*b₀)
    (r₁ + q₀*b₁+q₁*b₀) (r₂ + q₀*b₂+q₁*b₁+q₂*b₀)
    (r₃ + q₀*b₃+q₁*b₂+q₂*b₁+q₃*b₀)
  dsimp only at hc
  have hp := four_column_product q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ b₀ b₁ b₂ b₃
  rw [he] at hp
  have h₀ := Nat.mod_add_div (r₀ + q₀*b₀) 65536
  have h₁ := Nat.mod_add_div ((r₀+q₀*b₀)/65536 + r₁+q₀*b₁+q₁*b₀) 65536
  have h₂ := Nat.mod_add_div
    (((r₀+q₀*b₀)/65536 + r₁+q₀*b₁+q₁*b₀)/65536 +
      r₂+q₀*b₂+q₁*b₁+q₂*b₀) 65536
  have h₃ := Nat.mod_add_div
    (((((r₀+q₀*b₀)/65536 + r₁+q₀*b₁+q₁*b₀)/65536 +
      r₂+q₀*b₂+q₁*b₁+q₂*b₀)/65536) +
      r₃+q₀*b₃+q₁*b₂+q₂*b₁+q₃*b₀) 65536
  have hb₀ := Nat.mod_lt (r₀ + q₀*b₀) (by decide : 0 < 65536)
  have hb₁ := Nat.mod_lt ((r₀+q₀*b₀)/65536 + r₁+q₀*b₁+q₁*b₀)
    (by decide : 0 < 65536)
  have hb₂ := Nat.mod_lt
    (((r₀+q₀*b₀)/65536 + r₁+q₀*b₁+q₁*b₀)/65536 +
      r₂+q₀*b₂+q₁*b₁+q₂*b₀) (by decide : 0 < 65536)
  have hb₃ := Nat.mod_lt
    (((((r₀+q₀*b₀)/65536 + r₁+q₀*b₁+q₁*b₀)/65536 +
      r₂+q₀*b₂+q₁*b₁+q₂*b₀)/65536) +
      r₃+q₀*b₃+q₁*b₂+q₂*b₁+q₃*b₀) (by decide : 0 < 65536)
  simp only [assemble] at hp
  omega


set_option maxHeartbeats 2000000
/-- The four guarded low-column identities of the concrete 64-bit helper. -/
theorem sixty_four_bit_columns (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat)
    (hb : wordB 64 [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃] ≠ 0) :
    let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
    (∀ i < 4, carry 64 v i + rDigit 64 v i + convolution 64 v i =
      inputDigit 64 v i + 65536 * carry 64 v (i+1)) := by
  dsimp only
  let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
  have ha : wordA 64 v = assemble 65536
      [a₀%65536,a₁%65536,a₂%65536,a₃%65536] := by
    simp [v, wordA, normalize, radix, limbs]
  have hbd : wordB 64 v = assemble 65536
      [b₀%65536,b₁%65536,b₂%65536,b₃%65536] := by
    simp [v, wordB, normalize, radix, limbs]
  have habound : wordA 64 v < 65536 ^ 4 := by
    simpa [v, radix, limbs] using wordA_bound 64 v
  have hbbound : wordB 64 v < 65536 ^ 4 := by
    simpa [v, radix, limbs] using wordB_bound 64 v
  have hq : quotient 64 v < 65536 ^ 4 :=
    Nat.lt_of_le_of_lt (quotient_le 64 v hb) habound
  have hr : remainder 64 v < 65536 ^ 4 :=
    Nat.lt_trans (remainder_lt 64 v hb) hbbound
  have hqe := four_digit_expand 65536 (quotient 64 v) hq
  have hre := four_digit_expand 65536 (remainder 64 v) hr
  have he : assemble 65536 [qDigit 64 v 0,qDigit 64 v 1,
      qDigit 64 v 2,qDigit 64 v 3] *
      assemble 65536 [b₀%65536,b₁%65536,b₂%65536,b₃%65536] +
      assemble 65536 [rDigit 64 v 0,rDigit 64 v 1,
        rDigit 64 v 2,rDigit 64 v 3] =
      assemble 65536 [a₀%65536,a₁%65536,a₂%65536,a₃%65536] := by
    have hqeq : assemble 65536 [qDigit 64 v 0,qDigit 64 v 1,
        qDigit 64 v 2,qDigit 64 v 3] = quotient 64 v := by
      simpa [qDigit, radix] using hqe.symm
    have hreq : assemble 65536 [rDigit 64 v 0,rDigit 64 v 1,
        rDigit 64 v 2,rDigit 64 v 3] = remainder 64 v := by
      simpa [rDigit, radix] using hre.symm
    rw [hqeq, hreq, ← hbd, ← ha]
    simpa [Nat.mul_comm] using division_identity 64 v hb
  have hcore := four_column_eq_core (qDigit 64 v 0) (qDigit 64 v 1)
    (qDigit 64 v 2) (qDigit 64 v 3) (rDigit 64 v 0) (rDigit 64 v 1)
    (rDigit 64 v 2) (rDigit 64 v 3) (b₀%65536) (b₁%65536)
    (b₂%65536) (b₃%65536) (a₀%65536) (a₁%65536)
    (a₂%65536) (a₃%65536)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) he
  intro i hi
  have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi_cases with rfl | rfl | rfl | rfl
  all_goals simp [carry, convolution, bDigit, inputDigit, v, limbs, radix,
    show List.range 4 = [0,1,2,3] by decide] at hcore ⊢
  all_goals omega


/-- All strictly high diagonals vanish when the full product plus remainder
fits in four radix digits. They are nonnegative, hence cannot cancel. -/
theorem four_column_high_zero_core (q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃
    b₀ b₁ b₂ b₃ a₀ a₁ a₂ a₃ : Nat)
    (ha₀ : a₀ < 65536) (ha₁ : a₁ < 65536)
    (ha₂ : a₂ < 65536) (ha₃ : a₃ < 65536)
    (he : assemble 65536 [q₀,q₁,q₂,q₃] *
      assemble 65536 [b₀,b₁,b₂,b₃] + assemble 65536 [r₀,r₁,r₂,r₃] =
      assemble 65536 [a₀,a₁,a₂,a₃]) :
    q₁*b₃+q₂*b₂+q₃*b₁ = 0 ∧ q₂*b₃+q₃*b₂ = 0 ∧ q₃*b₃ = 0 := by
  have hp := four_column_product q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ b₀ b₁ b₂ b₃
  rw [he] at hp
  have hb : assemble 65536 [a₀,a₁,a₂,a₃] < 65536 ^ 4 := by
    apply assemble_bound 65536 [a₀,a₁,a₂,a₃] (by decide)
    intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    all_goals assumption
  omega


set_option maxHeartbeats 2000000
/-- Every convolution column beyond the four-digit word is identically zero. -/
theorem sixty_four_bit_high_convolution_zero (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat)
    (hb : wordB 64 [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃] ≠ 0) :
    let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
    convolution 64 v 4 = 0 ∧ convolution 64 v 5 = 0 ∧
      convolution 64 v 6 = 0 ∧ convolution 64 v 7 = 0 := by
  dsimp only
  let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
  have ha : wordA 64 v = assemble 65536
      [a₀%65536,a₁%65536,a₂%65536,a₃%65536] := by
    simp [v, wordA, normalize, radix, limbs]
  have hbd : wordB 64 v = assemble 65536
      [b₀%65536,b₁%65536,b₂%65536,b₃%65536] := by
    simp [v, wordB, normalize, radix, limbs]
  have habound : wordA 64 v < 65536 ^ 4 := by
    simpa [v, radix, limbs] using wordA_bound 64 v
  have hbbound : wordB 64 v < 65536 ^ 4 := by
    simpa [v, radix, limbs] using wordB_bound 64 v
  have hq : quotient 64 v < 65536 ^ 4 :=
    Nat.lt_of_le_of_lt (quotient_le 64 v hb) habound
  have hr : remainder 64 v < 65536 ^ 4 :=
    Nat.lt_trans (remainder_lt 64 v hb) hbbound
  have hqe := four_digit_expand 65536 (quotient 64 v) hq
  have hre := four_digit_expand 65536 (remainder 64 v) hr
  have he : assemble 65536 [qDigit 64 v 0,qDigit 64 v 1,
      qDigit 64 v 2,qDigit 64 v 3] *
      assemble 65536 [b₀%65536,b₁%65536,b₂%65536,b₃%65536] +
      assemble 65536 [rDigit 64 v 0,rDigit 64 v 1,
        rDigit 64 v 2,rDigit 64 v 3] =
      assemble 65536 [a₀%65536,a₁%65536,a₂%65536,a₃%65536] := by
    have hqeq : assemble 65536 [qDigit 64 v 0,qDigit 64 v 1,
        qDigit 64 v 2,qDigit 64 v 3] = quotient 64 v := by
      simpa [qDigit, radix] using hqe.symm
    have hreq : assemble 65536 [rDigit 64 v 0,rDigit 64 v 1,
        rDigit 64 v 2,rDigit 64 v 3] = remainder 64 v := by
      simpa [rDigit, radix] using hre.symm
    rw [hqeq, hreq, ← hbd, ← ha]
    simpa [Nat.mul_comm] using division_identity 64 v hb
  have hh := four_column_high_zero_core (qDigit 64 v 0) (qDigit 64 v 1)
    (qDigit 64 v 2) (qDigit 64 v 3) (rDigit 64 v 0) (rDigit 64 v 1)
    (rDigit 64 v 2) (rDigit 64 v 3) (b₀%65536) (b₁%65536)
    (b₂%65536) (b₃%65536) (a₀%65536) (a₁%65536)
    (a₂%65536) (a₃%65536)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) he
  have hrange : List.range 4 = [0,1,2,3] := by decide
  simp [convolution, hrange, bDigit, inputDigit, v, limbs, radix] at hh ⊢
  omega


/-- The actual high carry slots 4..8 all vanish; not merely the last slot. -/
theorem sixty_four_bit_high_carries_zero (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat)
    (hb : wordB 64 [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃] ≠ 0) :
    let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
    carry 64 v 4 = 0 ∧ carry 64 v 5 = 0 ∧ carry 64 v 6 = 0 ∧
      carry 64 v 7 = 0 ∧ carry 64 v 8 = 0 := by
  dsimp only
  let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
  have hc₄ : carry 64 v 4 = 0 := sixty_four_bit_carry_zero a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ hb
  obtain ⟨h₄, h₅, h₆, h₇⟩ :=
    sixty_four_bit_high_convolution_zero a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ hb
  change convolution 64 v 4 = 0 at h₄
  change convolution 64 v 5 = 0 at h₅
  change convolution 64 v 6 = 0 at h₆
  change convolution 64 v 7 = 0 at h₇
  have hc₅ : carry 64 v 5 = 0 := by
    change (carry 64 v 4 + (if 4 < limbs 64 then rDigit 64 v 4 else 0) +
      convolution 64 v 4) / radix 64 = 0
    simp [limbs, radix, hc₄, h₄]
  have hc₆ : carry 64 v 6 = 0 := by
    change (carry 64 v 5 + (if 5 < limbs 64 then rDigit 64 v 5 else 0) +
      convolution 64 v 5) / radix 64 = 0
    simp [limbs, radix, hc₅, h₅]
  have hc₇ : carry 64 v 7 = 0 := by
    change (carry 64 v 6 + (if 6 < limbs 64 then rDigit 64 v 6 else 0) +
      convolution 64 v 6) / radix 64 = 0
    simp [limbs, radix, hc₆, h₆]
  have hc₈ : carry 64 v 8 = 0 := by
    change (carry 64 v 7 + (if 7 < limbs 64 then rDigit 64 v 7 else 0) +
      convolution 64 v 7) / radix 64 = 0
    simp [limbs, radix, hc₇, h₇]
  exact ⟨hc₄, hc₅, hc₆, hc₇, hc₈⟩

/-- Every guarded high-column equation in the 64-bit machine is sound. -/
theorem sixty_four_bit_high_columns (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat)
    (hb : wordB 64 [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃] ≠ 0) :
    let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
    ∀ i, 4 ≤ i → i < 8 →
      carry 64 v i + convolution 64 v i = 65536 * carry 64 v (i+1) := by
  dsimp only
  let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
  obtain ⟨hc₄,hc₅,hc₆,hc₇,hc₈⟩ :=
    sixty_four_bit_high_carries_zero a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ hb
  obtain ⟨h₄,h₅,h₆,h₇⟩ :=
    sixty_four_bit_high_convolution_zero a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ hb
  intro i hlow hhigh
  have hi : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  all_goals simp [hc₄,hc₅,hc₆,hc₇,hc₈,h₄,h₅,h₆,h₇]


/-- Each convolution coefficient is bounded independently of the divisor:
normalization applies even to zero-divisor and out-of-domain input limbs. -/
theorem convolution_bound (w : Nat) (v : List Nat) (col : Nat) :
    convolution w v col ≤ limbs w * (radix w * (radix w - 1)) := by
  let base := radix w
  let cap := base * (base - 1)
  have hterm (j : Nat) :
      (if j ≤ col ∧ col - j < limbs w then
        qDigit w v j * bDigit w v (col-j) else 0) ≤ cap := by
    split
    · have hq : qDigit w v j ≤ base - 1 := by
        have h := qDigit_lt w v j
        dsimp [base]
        omega
      have hb : bDigit w v (col-j) ≤ base := by
        have h := Nat.mod_lt (v[limbs w + (col-j)]?.getD 0) (radix_pos w)
        dsimp [bDigit, inputDigit, base]
        omega
      have hm := Nat.mul_le_mul hq hb
      dsimp [cap]
      simpa [Nat.mul_comm] using hm
    · exact Nat.zero_le _
  have hsum (xs : List Nat) :
      (xs.map fun j => if j ≤ col ∧ col-j < limbs w then
        qDigit w v j * bDigit w v (col-j) else 0).sum ≤ xs.length * cap := by
    induction xs with
    | nil => simp
    | cons j xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have hadd := Nat.add_le_add (hterm j) ih
      omega
  simpa [convolution, cap, base] using hsum (List.range (limbs w))

/-- The TS rule's unconditional c_i ≤ n*base bound holds for every index,
including zero divisors, arbitrary length lists and every natural width. -/
theorem carry_bound (w : Nat) (v : List Nat) (i : Nat) :
    carry w v i ≤ limbs w * radix w := by
  let base := radix w
  let n := limbs w
  have hb : 0 < base := radix_pos w
  induction i with
  | zero => simp [carry]
  | succ i ih =>
    change carry w v i ≤ n * base at ih
    let r := if i < n then rDigit w v i else 0
    have hr : r < base := by
      by_cases h : i < n
      · simp only [r, if_pos h]
        exact rDigit_lt w v i
      · simp only [r, if_neg h]
        exact hb
    have hconv : convolution w v i ≤ n * (base * (base - 1)) :=
      convolution_bound w v i
    have hpre : base - 1 + 1 = base := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hb))
    have halg : n * base + n * (base * (base - 1)) + base =
        base * (n * base + 1) := by
      calc
        n * base + n * (base * (base - 1)) + base =
            (n * base) * (1 + (base - 1)) + base := by
              simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ = base * (n * base + 1) := by
          rw [Nat.add_comm 1 (base-1), hpre]
          simp [Nat.mul_add, Nat.mul_comm, Nat.mul_assoc]
    have htotal : carry w v i + r + convolution w v i <
        base * (n * base + 1) := by omega
    have hq : (carry w v i + r + convolution w v i) / base <
        n * base + 1 := (Nat.div_lt_iff_lt_mul hb).2 (by simpa [Nat.mul_comm] using htotal)
    change (carry w v i + r + convolution w v i) / base ≤ n * base
    omega


/-- The concrete one-limb machine's two convolution columns, universally in
both operands; this covers the 8- and 16-bit specializations. -/
theorem single_limb_columns (w a b : Nat) (hn : limbs w = 1)
    (hb : b % radix w ≠ 0) :
    let v := [a,b]
    (carry w v 0 + rDigit w v 0 + convolution w v 0 =
      inputDigit w v 0 + radix w * carry w v 1) ∧
    (carry w v 1 + convolution w v 1 = radix w * carry w v 2) := by
  dsimp only
  let v := [a,b]
  have ha : wordA w v = a % radix w := by
    simp [v, wordA, normalize, assemble, hn]
  have hbd : wordB w v = b % radix w := by
    simp [v, wordB, normalize, assemble, hn]
  have hne : wordB w v ≠ 0 := by simpa [hbd, v] using hb
  have hid := division_identity w v hne
  have hq : quotient w v < radix w := by
    have hle := quotient_le w v hne
    have hm := Nat.mod_lt a (radix_pos w)
    omega
  have hr : remainder w v < radix w := by
    have hle := remainder_lt w v hne
    have hm := Nat.mod_lt b (radix_pos w)
    omega
  have hq₀ : qDigit w v 0 = quotient w v := by
    simp [qDigit, digit, Nat.mod_eq_of_lt hq]
  have hr₀ : rDigit w v 0 = remainder w v := by
    simp [rDigit, digit, Nat.mod_eq_of_lt hr]
  have hc₁ : carry w v 1 = 0 := by
    simpa [v] using single_limb_carry_zero w a b hn hb
  have hconv₀ : convolution w v 0 = quotient w v * (b % radix w) := by
    simp [convolution, hn, hq₀, bDigit, inputDigit, v]
  have hconv₁ : convolution w v 1 = 0 := by
    simp [convolution, hn]
  have hc₂ : carry w v 2 = 0 := by
    change (carry w v 1 + (if 1 < limbs w then rDigit w v 1 else 0) +
      convolution w v 1) / radix w = 0
    simp [hn, hc₁, hconv₁]
  dsimp only [v] at *
  constructor
  · have hi : quotient w [a,b] * (b % radix w) + remainder w [a,b] = a % radix w := by
      simpa [ha, hbd, Nat.mul_comm] using hid
    simp [carry_zero, hr₀, hconv₀, hc₁, inputDigit]
    omega
  · simpa [hc₁, hc₂, hconv₁]


/-- Two bounded output digits uniquely determine the two low-column equations. -/
theorem two_column_eq_core (q₀ q₁ r₀ r₁ b₀ b₁ a₀ a₁ : Nat)
    (ha₀ : a₀ < 65536) (ha₁ : a₁ < 65536)
    (he : (q₀ + 65536*q₁) * (b₀ + 65536*b₁) +
      (r₀ + 65536*r₁) = a₀ + 65536*a₁) :
    let t₀ := r₀ + q₀*b₀
    let t₁ := r₁ + q₀*b₁ + q₁*b₀
    let c₁ := t₀ / 65536
    let c₂ := (c₁ + t₁) / 65536
    t₀ = a₀ + 65536*c₁ ∧ c₁+t₁ = a₁ + 65536*c₂ := by
  dsimp only
  have hring : (q₀ + 65536*q₁) * (b₀ + 65536*b₁) +
      (r₀ + 65536*r₁) =
      (r₀ + q₀*b₀) + 65536*(r₁+q₀*b₁+q₁*b₀) +
      65536^2*(q₁*b₁) := by
    simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hprod := hring.symm.trans he
  have hd := Nat.mod_add_div (r₀ + q₀*b₀) 65536
  have hd₁ := Nat.mod_add_div
    ((r₀ + q₀*b₀) / 65536 + r₁+q₀*b₁+q₁*b₀) 65536
  have hb₀ := Nat.mod_lt (r₀ + q₀*b₀) (by decide : 0 < 65536)
  have hb₁ := Nat.mod_lt
    ((r₀ + q₀*b₀) / 65536 + r₁+q₀*b₁+q₁*b₀) (by decide : 0 < 65536)
  have hcarry := two_column_carry_core 65536 q₀ q₁ r₀ r₁ b₀ b₁ a₀ a₁
    (by decide) ha₀ ha₁ he
  omega


set_option maxHeartbeats 2000000
/-- Both guarded low columns of the actual 32-bit helper. -/
theorem thirty_two_bit_low_columns (a₀ a₁ b₀ b₁ : Nat)
    (hb : wordB 32 [a₀,a₁,b₀,b₁] ≠ 0) :
    let v := [a₀,a₁,b₀,b₁]
    ∀ i < 2, carry 32 v i + rDigit 32 v i + convolution 32 v i =
      inputDigit 32 v i + 65536*carry 32 v (i+1) := by
  dsimp only
  let v := [a₀, a₁, b₀, b₁]
  have ha : wordA 32 v = a₀ % 65536 + 65536 * (a₁ % 65536) := by
    simp [v, wordA, normalize, assemble, radix, limbs]
  have hbd : wordB 32 v = b₀ % 65536 + 65536 * (b₁ % 65536) := by
    simp [v, wordB, normalize, assemble, radix, limbs]
  have habound : wordA 32 v < 65536 ^ 2 := by
    simpa [v, radix, limbs] using wordA_bound 32 v
  have hbbound : wordB 32 v < 65536 ^ 2 := by
    simpa [v, radix, limbs] using wordB_bound 32 v
  have hq : quotient 32 v < 65536 ^ 2 :=
    Nat.lt_of_le_of_lt (quotient_le 32 v hb) habound
  have hr : remainder 32 v < 65536 ^ 2 :=
    Nat.lt_trans (remainder_lt 32 v hb) hbbound
  have hqe := two_digit_expand 65536 (quotient 32 v) hq
  have hre := two_digit_expand 65536 (remainder 32 v) hr
  have he : (qDigit 32 v 0 + 65536*qDigit 32 v 1) *
      (b₀ % 65536 + 65536*(b₁ % 65536)) +
      (rDigit 32 v 0 + 65536*rDigit 32 v 1) =
      a₀ % 65536 + 65536*(a₁ % 65536) := by
    have hqeq : qDigit 32 v 0 + 65536*qDigit 32 v 1 = quotient 32 v := by
      simpa [qDigit, digit, radix] using hqe.symm
    have hreq : rDigit 32 v 0 + 65536*rDigit 32 v 1 = remainder 32 v := by
      simpa [rDigit, digit, radix] using hre.symm
    rw [hqeq, hreq, ← hbd, ← ha]
    simpa [Nat.mul_comm] using division_identity 32 v hb
  have hcore := two_column_eq_core (qDigit 32 v 0) (qDigit 32 v 1)
    (rDigit 32 v 0) (rDigit 32 v 1) (b₀ % 65536) (b₁ % 65536)
    (a₀ % 65536) (a₁ % 65536)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) he
  intro i hi
  have hs : i = 0 ∨ i = 1 := by omega
  rcases hs with rfl | rfl
  all_goals simp [carry, convolution, bDigit, inputDigit, v, limbs, radix,
    show List.range 2 = [0,1] by decide] at hcore ⊢
  all_goals omega


/-- The unique high diagonal of a two-limb product cannot fit in its word. -/
theorem two_column_high_zero_core (q₀ q₁ r₀ r₁ b₀ b₁ a₀ a₁ : Nat)
    (ha₀ : a₀ < 65536) (ha₁ : a₁ < 65536)
    (he : (q₀ + 65536*q₁) * (b₀ + 65536*b₁) +
      (r₀ + 65536*r₁) = a₀ + 65536*a₁) : q₁*b₁ = 0 := by
  have hp : (q₀ + 65536*q₁) * (b₀ + 65536*b₁) +
      (r₀ + 65536*r₁) =
      (r₀ + q₀*b₀) + 65536*(r₁+q₀*b₁+q₁*b₀) +
      65536^2*(q₁*b₁) := by
    simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hs : a₀ + 65536*a₁ < 65536^2 := by omega
  have ht := hp.symm.trans he
  omega


/-- Both guarded high columns and last carry of the actual 32-bit helper. -/
theorem thirty_two_bit_high_columns (a₀ a₁ b₀ b₁ : Nat)
    (hb : wordB 32 [a₀,a₁,b₀,b₁] ≠ 0) :
    let v := [a₀,a₁,b₀,b₁]
    carry 32 v 2 + convolution 32 v 2 = 65536*carry 32 v 3 ∧
    carry 32 v 3 + convolution 32 v 3 = 65536*carry 32 v 4 ∧
    carry 32 v 4 = 0 := by
  dsimp only
  let v := [a₀, a₁, b₀, b₁]
  have ha : wordA 32 v = a₀ % 65536 + 65536 * (a₁ % 65536) := by
    simp [v, wordA, normalize, assemble, radix, limbs]
  have hbd : wordB 32 v = b₀ % 65536 + 65536 * (b₁ % 65536) := by
    simp [v, wordB, normalize, assemble, radix, limbs]
  have habound : wordA 32 v < 65536 ^ 2 := by
    simpa [v, radix, limbs] using wordA_bound 32 v
  have hbbound : wordB 32 v < 65536 ^ 2 := by
    simpa [v, radix, limbs] using wordB_bound 32 v
  have hq : quotient 32 v < 65536 ^ 2 :=
    Nat.lt_of_le_of_lt (quotient_le 32 v hb) habound
  have hr : remainder 32 v < 65536 ^ 2 :=
    Nat.lt_trans (remainder_lt 32 v hb) hbbound
  have hqe := two_digit_expand 65536 (quotient 32 v) hq
  have hre := two_digit_expand 65536 (remainder 32 v) hr
  have he : (qDigit 32 v 0 + 65536*qDigit 32 v 1) *
      (b₀ % 65536 + 65536*(b₁ % 65536)) +
      (rDigit 32 v 0 + 65536*rDigit 32 v 1) =
      a₀ % 65536 + 65536*(a₁ % 65536) := by
    have hqeq : qDigit 32 v 0 + 65536*qDigit 32 v 1 = quotient 32 v := by
      simpa [qDigit, digit, radix] using hqe.symm
    have hreq : rDigit 32 v 0 + 65536*rDigit 32 v 1 = remainder 32 v := by
      simpa [rDigit, digit, radix] using hre.symm
    rw [hqeq, hreq, ← hbd, ← ha]
    simpa [Nat.mul_comm] using division_identity 32 v hb
  have hhigh := two_column_high_zero_core (qDigit 32 v 0) (qDigit 32 v 1)
    (rDigit 32 v 0) (rDigit 32 v 1) (b₀%65536) (b₁%65536)
    (a₀%65536) (a₁%65536)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) he
  have h₂ : convolution 32 v 2 = 0 := by
    have hrange : List.range 2 = [0,1] := by decide
    simpa [convolution, hrange, bDigit, inputDigit, v, limbs, radix] using hhigh
  have h₃ : convolution 32 v 3 = 0 := by
    simp [convolution, show List.range 2 = [0,1] by decide, limbs]
  have hc₂ : carry 32 v 2 = 0 := thirty_two_bit_carry_zero a₀ a₁ b₀ b₁ hb
  have hc₃ : carry 32 v 3 = 0 := by
    change (carry 32 v 2 + (if 2 < limbs 32 then rDigit 32 v 2 else 0) +
      convolution 32 v 2) / radix 32 = 0
    simp [limbs, radix, hc₂, h₂]
  have hc₄ : carry 32 v 4 = 0 := by
    change (carry 32 v 3 + (if 3 < limbs 32 then rDigit 32 v 3 else 0) +
      convolution 32 v 3) / radix 32 = 0
    simp [limbs, radix, hc₃, h₃]
  dsimp only [v] at *
  simpa [hc₂,hc₃,hc₄,h₂,h₃]

#print axioms WordDivision.thirty_two_bit_high_columns
#print axioms WordDivision.two_column_high_zero_core
#print axioms WordDivision.thirty_two_bit_low_columns
#print axioms WordDivision.two_column_eq_core
#print axioms WordDivision.single_limb_columns
#print axioms WordDivision.carry_bound
#print axioms WordDivision.sixty_four_bit_high_columns
#print axioms WordDivision.sixty_four_bit_high_carries_zero
#print axioms WordDivision.sixty_four_bit_high_convolution_zero
#print axioms WordDivision.four_column_high_zero_core
#print axioms WordDivision.sixty_four_bit_columns
#print axioms WordDivision.zero_divisor_carry
#print axioms WordDivision.single_limb_carry_zero
#print axioms WordDivision.thirty_two_bit_carry_zero
#print axioms WordDivision.sixty_four_bit_carry_zero
#print axioms WordDivision.four_column_carry_core
#print axioms WordDivision.division_identity
#print axioms WordDivision.remainder_lt
#print axioms WordDivision.quotient_le
end WordDivision
