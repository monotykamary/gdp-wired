import Std

/-! The low-diagonal/carry part of `FixedWord.mul` in `core/fixed-integers.ts`.
The inputs here are unsigned limb *magnitudes*. Signed magnitude conversion,
negation of the low word, overflow detection, saturation and trapping are not
covered by these unsigned low-WRAP identities. -/
namespace FixedLimbMul

private def base : Nat := 65536

def word1 (a₀ : Nat) : Nat := a₀
def word2 (a₀ a₁ : Nat) : Nat := a₀ + base * a₁
def word4 (a₀ a₁ a₂ a₃ : Nat) : Nat :=
  a₀ + base * (a₁ + base * (a₂ + base * a₃))

/-- The first four columns of the actual multiplication loop; the quotient of
one column is the initial carry of the next. -/
def columns4 (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat) : Nat :=
  let c₀ := a₀ * b₀
  let c₁ := c₀ / base + a₀ * b₁ + a₁ * b₀
  let c₂ := c₁ / base + a₀ * b₂ + a₁ * b₁ + a₂ * b₀
  let c₃ := c₂ / base + a₀ * b₃ + a₁ * b₂ + a₂ * b₁ + a₃ * b₀
  c₀ % base + base * (c₁ % base + base * (c₂ % base + base * (c₃ % base)))

private def low4 (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat) : Nat :=
  a₀*b₀ + base*(a₀*b₁+a₁*b₀) +
    base^2*(a₀*b₂+a₁*b₁+a₂*b₀) +
    base^3*(a₀*b₃+a₁*b₂+a₂*b₁+a₃*b₀)

private def high4 (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat) : Nat :=
  a₁*b₃+a₂*b₂+a₃*b₁ + base*(a₂*b₃+a₃*b₂) + base^2*(a₃*b₃)

/-- Polynomial multiplication, retaining the high diagonal terms without
subtraction or a nonlinear arithmetic decision procedure. -/
private theorem product4 (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat) :
    word4 a₀ a₁ a₂ a₃ * word4 b₀ b₁ b₂ b₃ =
      low4 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ +
      base^4 * high4 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ := by
  simp [word4, low4, high4, base, Nat.pow_succ, Nat.mul_add, Nat.add_mul,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] <;> omega

private theorem carry4 (t₀ t₁ t₂ t₃ : Nat) :
    let c₀ := t₀
    let c₁ := c₀ / base + t₁
    let c₂ := c₁ / base + t₂
    let c₃ := c₂ / base + t₃
    c₀ % base + base * (c₁ % base + base * (c₂ % base + base * (c₃ % base))) +
      base^4 * (c₃ / base) =
      t₀ + base*t₁ + base^2*t₂ + base^3*t₃ := by
  dsimp [base]
  have h₀ := Nat.mod_add_div t₀ 65536
  have h₁ := Nat.mod_add_div (t₀ / 65536 + t₁) 65536
  have h₂ := Nat.mod_add_div ((t₀ / 65536 + t₁) / 65536 + t₂) 65536
  have h₃ := Nat.mod_add_div
    (((t₀ / 65536 + t₁) / 65536 + t₂) / 65536 + t₃) 65536
  omega

private theorem columns4_reconstruct (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat) :
    columns4 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ +
      base^4 * (((((a₀*b₀ / base + a₀*b₁ + a₁*b₀) / base +
        a₀*b₂+a₁*b₁+a₂*b₀) / base +
        a₀*b₃+a₁*b₂+a₂*b₁+a₃*b₀) / base)) =
      low4 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ := by
  simpa [columns4, low4, Nat.add_assoc, Nat.mul_add, Nat.mul_assoc] using
    carry4 (a₀*b₀) (a₀*b₁+a₁*b₀) (a₀*b₂+a₁*b₁+a₂*b₀)
      (a₀*b₃+a₁*b₂+a₂*b₁+a₃*b₀)

/-- Four emitted low digits reconstruct the product modulo 2^64. No digit
bounds are needed: each emitted digit is a remainder by the radix. -/
theorem four_limb_mul_wrap (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat) :
    columns4 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ % 2^64 =
      (word4 a₀ a₁ a₂ a₃ * word4 b₀ b₁ b₂ b₃) % 2^64 := by
  have hc := columns4_reconstruct a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
  have hp := product4 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
  have hm : base^4 = 2^64 := by decide
  rw [← hm]
  have h := congrArg (fun x : Nat => x % base^4) hc
  have hpmod := congrArg (fun x : Nat => x % base^4) hp
  dsimp [base] at h hpmod ⊢
  omega

/-- One radix-65536 column is the actual 16-bit specialization. -/
theorem one_limb_mul_wrap (a₀ b₀ : Nat) :
    (a₀*b₀ % base) % 2^16 = (word1 a₀ * word1 b₀) % 2^16 := by
  simp [word1, base, show (65536 : Nat) = 2^16 by decide, Nat.mod_mod]

/-- Two low columns are the actual 32-bit specialization. -/
theorem two_limb_mul_wrap (a₀ a₁ b₀ b₁ : Nat) :
    let c₀ := a₀*b₀
    let c₁ := c₀ / base + a₀*b₁ + a₁*b₀
    (c₀ % base + base*(c₁ % base)) % 2^32 =
      (word2 a₀ a₁ * word2 b₀ b₁) % 2^32 := by
  dsimp only
  have h₀ := Nat.mod_add_div (a₀*b₀) base
  have h₁ := Nat.mod_add_div (a₀*b₀ / base + a₀*b₁ + a₁*b₀) base
  have hp : word2 a₀ a₁ * word2 b₀ b₁ =
      a₀*b₀ + base*(a₀*b₁+a₁*b₀) + base^2*(a₁*b₁) := by
    simp [word2, base, Nat.pow_succ, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] <;> omega
  have hm : base^2 = 2^32 := by decide
  rw [← hm, hp]
  have he : a₀*b₀ % base + base*((a₀*b₀ / base + a₀*b₁+a₁*b₀) % base) +
      base^2*((a₀*b₀ / base + a₀*b₁+a₁*b₀) / base) =
      a₀*b₀ + base*(a₀*b₁+a₁*b₀) := by
    dsimp [base] at *
    omega
  dsimp [base] at he ⊢
  omega

/-- Width eight uses the single radix-256 column, not radix 65536. -/
theorem eight_bit_mul_wrap (a₀ b₀ : Nat) :
    (a₀*b₀ % 256) % 2^8 = (a₀*b₀) % 2^8 := by
  simp [show (256 : Nat) = 2^8 by decide, Nat.mod_mod]

#print axioms FixedLimbMul.four_limb_mul_wrap
#print axioms FixedLimbMul.two_limb_mul_wrap
#print axioms FixedLimbMul.one_limb_mul_wrap
#print axioms FixedLimbMul.eight_bit_mul_wrap
end FixedLimbMul
