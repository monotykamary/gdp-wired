import RadixKeySyntax

/-! Family-local, typed prefix/tail candidate syntax, per t11's contract.
No numeric/tuple equivalence or packed-order transport is asserted. -/
namespace Bapa.PaxosEprPrefixTail
open Kern RadixKeySyntax

inductive Error where
  | invalidArity
  | expectedPrefixTail
  | wrongCoefficient (actual expected : Nat)
  | key (reason : RadixKeySyntax.Error)
  deriving Repr, BEq

def prefixTailParts (radix prefixArity tailArity : Nat)
    (bindings : List RawAddress) (key : E) : Except Error (List E) := do
  if prefixArity == 0 || tailArity == 0 then throw .invalidArity
  match key with
  | .add (.mul coefficient headExpr) tail =>
    if coefficient != radix ^ tailArity then
      throw (.wrongCoefficient coefficient (radix ^ tailArity))
    let front ← (keyParts radix bindings prefixArity headExpr).mapError Error.key
    let back ← (keyParts radix bindings tailArity tail).mapError Error.key
    return front ++ back
  | _ => throw .expectedPrefixTail

def candidate (radix prefixArity tailArity : Nat)
    (bindings : List RawAddress) (key : E) : Except Error E :=
  (prefixTailParts radix prefixArity tailArity bindings key).map tuple

def accepted (r : Except Error E) (expected : E) : Bool :=
  match r with | .ok e => beqE e expected | .error _ => false

def refused (r : Except Error E) : Bool :=
  match r with | .ok _ => false | .error _ => true

def raw : E := .add (.mul 4096 (.var 9)) (.var 133)
def bindings : List RawAddress := [⟨133,2,[.var 133,.var 1000001]⟩]

theorem typed_tail : accepted (candidate 64 1 2 bindings raw)
    (.tup (.var 9) (.tup (.var 133) (.var 1000001))) = true := by decide +kernel

theorem explicit_tail : accepted
    (candidate 64 1 2 [] (.add (.mul 4096 (.var 9)) (.add (.mul 64 (.var 4)) (.var 5))))
    (.tup (.var 9) (.tup (.var 4) (.var 5))) = true := by decide +kernel

theorem untyped_tail_refused : refused (candidate 64 1 2 [] raw) = true := by decide +kernel

theorem wrong_coefficient_refused : refused
    (candidate 64 1 2 bindings (.add (.mul 64 (.var 9)) (.var 133))) = true := by decide +kernel

theorem malformed_binding_refused : refused
    (candidate 64 1 2 [⟨133,2,[.var 133]⟩] raw) = true := by decide +kernel

theorem zero_arity_refused : refused (candidate 64 0 2 bindings raw) = true := by decide +kernel

#print axioms typed_tail
#print axioms explicit_tail
#print axioms untyped_tail_refused
#print axioms wrong_coefficient_refused
#print axioms malformed_binding_refused
#print axioms zero_arity_refused
end Bapa.PaxosEprPrefixTail
