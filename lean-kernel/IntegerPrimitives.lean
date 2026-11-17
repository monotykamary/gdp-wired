import Init.Data.BitVec.Lemmas
import Init.Data.Int.DivMod
import Init.Data.SInt
import Init.Data.UInt

/-! Exact fixed-width integer semantics. Inputs are mathematical integers; except for
`cast`, an operand outside the target interval is rejected rather than normalized.
Division by zero and signed MIN / -1 trapping are checked before Lean's totalized
integer division can be evaluated. All wrapping goes through the standard BitVec. -/
namespace IntegerPrimitives

-- Except does not ship a DecidableEq instance in this pinned Init surface.
-- Deriving constructs an ordinary kernel-checkable decision procedure.
deriving instance DecidableEq for Except

inductive Operation where
  | add | sub | mul | neg | cast | div | rem
  deriving DecidableEq, Repr

inductive Overflow where
  | WRAP | SATURATE | TRAP
  deriving DecidableEq, Repr

inductive Division where
  | FLOOR | TRUNCATING | EUCLIDEAN
  deriving DecidableEq, Repr, Inhabited

inductive Failure where
  | invalidSpec | invalidInput | divisionByZero | overflow
  deriving DecidableEq, Repr

structure PrimitiveSpec where
  width : Nat
  signed : Bool
  operation : Operation
  overflow : Overflow
  division : Option Division := none
  deriving DecidableEq, Repr

def validWidth (w : Nat) : Bool := w == 8 || w == 16 || w == 32 || w == 64

def lower (s : PrimitiveSpec) : Int :=
  if s.signed then -(Int.ofNat (2 ^ (s.width - 1))) else 0

def upper (s : PrimitiveSpec) : Int :=
  if s.signed then Int.ofNat (2 ^ (s.width - 1)) - 1
  else Int.ofNat (2 ^ s.width) - 1

def inRange (s : PrimitiveSpec) (x : Int) : Bool :=
  decide (lower s ≤ x) && decide (x ≤ upper s)

def decode (signed : Bool) (v : BitVec w) : Int :=
  if signed then v.toInt else Int.ofNat v.toNat

def wrap (s : PrimitiveSpec) (x : Int) : Int :=
  decode s.signed (BitVec.ofInt s.width x)

/-- These bridges are to the actual standard BitVec operations, not a parallel
model of modular arithmetic. They hold for arbitrary width and arbitrary Ints. -/
theorem wrap_add (w : Nat) (signed : Bool) (a b : Int) :
    decode signed (BitVec.ofInt w (a + b)) =
      decode signed (BitVec.ofInt w a + BitVec.ofInt w b) := by
  rw [BitVec.ofInt_add]

theorem wrap_mul (w : Nat) (signed : Bool) (a b : Int) :
    decode signed (BitVec.ofInt w (a * b)) =
      decode signed (BitVec.ofInt w a * BitVec.ofInt w b) := by
  rw [BitVec.ofInt_mul]

theorem wrap_neg (w : Nat) (signed : Bool) (a : Int) :
    decode signed (BitVec.ofInt w (-a)) =
      decode signed (-BitVec.ofInt w a) := by
  rw [BitVec.ofInt_neg]

theorem wrap_sub (w : Nat) (signed : Bool) (a b : Int) :
    decode signed (BitVec.ofInt w (a - b)) =
      decode signed (BitVec.ofInt w a - BitVec.ofInt w b) := by
  simp only [Int.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]

-- Native IntN/UIntN representations expose these same standard bitvectors.
example (z : Int) : (Int8.ofInt z).toBitVec = BitVec.ofInt 8 z := rfl
example (z : Int) : (Int16.ofInt z).toBitVec = BitVec.ofInt 16 z := rfl
example (z : Int) : (Int32.ofInt z).toBitVec = BitVec.ofInt 32 z := rfl
example (z : Int) : (Int64.ofInt z).toBitVec = BitVec.ofInt 64 z := rfl
example (z : Int) : (⟨BitVec.ofInt 8 z⟩ : UInt8).toBitVec = BitVec.ofInt 8 z := rfl
example (z : Int) : (⟨BitVec.ofInt 16 z⟩ : UInt16).toBitVec = BitVec.ofInt 16 z := rfl
example (z : Int) : (⟨BitVec.ofInt 32 z⟩ : UInt32).toBitVec = BitVec.ofInt 32 z := rfl
example (z : Int) : (⟨BitVec.ofInt 64 z⟩ : UInt64).toBitVec = BitVec.ofInt 64 z := rfl

/-- Division modes use the exact three standard Int division/remainder pairs.
The caller must reject zero first: every Lean Int division is total at zero. -/
def quotient (mode : Division) (a b : Int) : Int :=
  match mode with
  | .FLOOR => Int.fdiv a b
  | .TRUNCATING => Int.tdiv a b
  | .EUCLIDEAN => Int.ediv a b

def remainder (mode : Division) (a b : Int) : Int :=
  match mode with
  | .FLOOR => Int.fmod a b
  | .TRUNCATING => Int.tmod a b
  | .EUCLIDEAN => Int.emod a b

/-- `division` is mandatory precisely for div/rem. The input restriction on
non-casts prevents an implicit normalization before the operation. -/
def validSpec (s : PrimitiveSpec) : Bool :=
  validWidth s.width &&
    (if s.operation == .div || s.operation == .rem
      then s.division.isSome else s.division.isNone)

def needsRight (op : Operation) : Bool :=
  op == .add || op == .sub || op == .mul || op == .div || op == .rem

def finish (s : PrimitiveSpec) (x : Int) : Except Failure Int :=
  if inRange s x then .ok x
  else match s.overflow with
    | .WRAP => .ok (wrap s x)
    | .SATURATE => .ok (if x < lower s then lower s else upper s)
    | .TRAP => .error .overflow

/-- Pair-level MIN / -1 overflow is an error for BOTH div and rem in TRAP mode.
WRAP/SATURATE remainder is zero, while quotient goes through `finish`. -/
def evaluate (s : PrimitiveSpec) (a : Int) (b : Option Int := none) : Except Failure Int := Id.run do
  if !validSpec s || b.isSome != needsRight s.operation then
    return .error .invalidSpec
  if (s.operation != .cast && !inRange s a) ||
      (needsRight s.operation && !inRange s b.get!) then
    return .error .invalidInput
  if s.operation == .div || s.operation == .rem then
    let y := b.get!
    if y == 0 then return .error .divisionByZero
    if s.signed && a == lower s && y == -1 then
      if s.overflow == .TRAP then return .error .overflow
      if s.operation == .rem then return .ok 0
    let mode := s.division.get!
    return finish s (if s.operation == .div then quotient mode a y else remainder mode a y)
  let raw := match s.operation with
    | .add => a + b.get!
    | .sub => a - b.get!
    | .mul => a * b.get!
    | .neg => -a
    | .cast => a
    | .div | .rem => 0 -- unreachable after the division branch
  return finish s raw

end IntegerPrimitives
