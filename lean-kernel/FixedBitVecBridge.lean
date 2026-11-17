import FixedLimbBridge

/-! The actual low limbs emitted by `addCarry` represent standard Lean bitvector
addition. The proof is parametric in the number of radix-65536 limbs; signed
interpretation is only a view of the same standard bitvector. -/
namespace FixedBitVecBridge

private theorem radix_pow (n : Nat) : 65536 ^ n = 2 ^ (16 * n) := by
  rw [show (65536 : Nat) = 2 ^ 16 by decide, Nat.pow_mul]

/-- The low output of the real little-endian carry loop equals standard
`BitVec` addition at exactly sixteen bits per input limb. The equality
of lengths is necessary because the implementation truncates on a mismatch. -/
theorem addCarry_bitvec (a b : List Nat) (h : a.length = b.length) :
    BitVec.ofNat (16 * a.length) (FixedLimbBridge.assemble (FixedLimbBridge.addCarry a b 0).1) =
      BitVec.ofNat (16 * a.length) (FixedLimbBridge.assemble a) +
        BitVec.ofNat (16 * a.length) (FixedLimbBridge.assemble b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
  rw [← radix_pow a.length]
  simpa [FixedLimbBridge.radix, Nat.add_mod, Nat.mod_mod] using FixedLimbBridge.addCarry_wrap a b h

/-- Signed and unsigned decoding both interpret the very same standard result;
no second signed arithmetic semantics is introduced. -/
theorem addCarry_decode (signed : Bool) (a b : List Nat)
    (h : a.length = b.length) :
    IntegerPrimitives.decode signed
      (BitVec.ofNat (16 * a.length)
        (FixedLimbBridge.assemble (FixedLimbBridge.addCarry a b 0).1)) =
      IntegerPrimitives.decode signed
        (BitVec.ofNat (16 * a.length) (FixedLimbBridge.assemble a) +
          BitVec.ofNat (16 * a.length) (FixedLimbBridge.assemble b)) := by
  rw [addCarry_bitvec a b h]

/-- The signed view is exactly standard `BitVec.toInt`. -/
theorem addCarry_toInt (a b : List Nat) (h : a.length = b.length) :
    (BitVec.ofNat (16 * a.length)
      (FixedLimbBridge.assemble (FixedLimbBridge.addCarry a b 0).1)).toInt =
      (BitVec.ofNat (16 * a.length) (FixedLimbBridge.assemble a) +
        BitVec.ofNat (16 * a.length) (FixedLimbBridge.assemble b)).toInt := by
  rw [addCarry_bitvec a b h]

theorem one_limb_add_bitvec (a₀ b₀ : Nat) :
    BitVec.ofNat 16 (FixedLimbBridge.assemble
      (FixedLimbBridge.addCarry [a₀] [b₀] 0).1) =
      BitVec.ofNat 16 (FixedLimbBridge.assemble [a₀]) +
        BitVec.ofNat 16 (FixedLimbBridge.assemble [b₀]) := by
  simpa using addCarry_bitvec [a₀] [b₀] (by rfl)

theorem two_limb_add_bitvec (a₀ a₁ b₀ b₁ : Nat) :
    BitVec.ofNat 32 (FixedLimbBridge.assemble
      (FixedLimbBridge.addCarry [a₀, a₁] [b₀, b₁] 0).1) =
      BitVec.ofNat 32 (FixedLimbBridge.assemble [a₀, a₁]) +
        BitVec.ofNat 32 (FixedLimbBridge.assemble [b₀, b₁]) := by
  simpa using addCarry_bitvec [a₀, a₁] [b₀, b₁] (by rfl)

theorem four_limb_add_bitvec (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat) :
    BitVec.ofNat 64 (FixedLimbBridge.assemble
      (FixedLimbBridge.addCarry [a₀, a₁, a₂, a₃] [b₀, b₁, b₂, b₃] 0).1) =
      BitVec.ofNat 64 (FixedLimbBridge.assemble [a₀, a₁, a₂, a₃]) +
        BitVec.ofNat 64 (FixedLimbBridge.assemble [b₀, b₁, b₂, b₃]) := by
  simpa using addCarry_bitvec [a₀, a₁, a₂, a₃] [b₀, b₁, b₂, b₃] (by rfl)

end FixedBitVecBridge
