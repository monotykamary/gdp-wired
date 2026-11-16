import Kernel

/-! The key/binder layer of radix-to-tuple certificate translation.
This does NOT yet translate tables, law instances or arithmetic trees and must
not be used to claim a re-keyed family. Unknown whole-address variables fail
closed; their typed component binders must be supplied by the caller. -/
namespace Bapa.RadixKeySyntax
open Kern

structure RawAddress where
  variableId : Nat
  arity : Nat
  components : List E

inductive Error where
  | zeroRadix
  | needBinderExpansion (variableId arity : Nat)
  | malformedBinder (variableId expected actual : Nat)
  | unsupportedKey (arity : Nat)
  deriving Repr, BEq

def tuple : List E → E
  | [] => .const 0
  | [a] => a
  | a :: rest => .tup a (tuple rest)

def tupleParts : E → List E
  | .tup a b => a :: tupleParts b
  | e => [e]

def literalParts (radix : Nat) : Nat → Nat → List E
  | 0, _ => []
  | 1, n => [.const n]
  | arity + 2, n => literalParts radix (arity + 1) (n / radix) ++ [.const (n % radix)]

/-- Read a known Horner-form packed address. The flattened arity-three form
emitted by the retained 0.49 certificates is supported explicitly too. -/
def keyParts (radix : Nat) (bindings : List RawAddress) : Nat → E → Except Error (List E)
  | 0, _ => .error (.unsupportedKey 0)
  | 1, e => .ok [e]
  | arity + 2, e =>
    if radix = 0 then .error .zeroRadix else
    match e with
    | .var v =>
      match bindings.find? (fun b => b.variableId == v && b.arity == arity + 2) with
      | none => .error (.needBinderExpansion v (arity + 2))
      | some b => if b.components.length = arity + 2 then .ok b.components
          else .error (.malformedBinder v (arity + 2) b.components.length)
    | .const n => .ok (literalParts radix (arity + 2) n)
    | .tup _ _ =>
      let ps := tupleParts e
      if ps.length = arity + 2 then .ok ps else .error (.unsupportedKey (arity + 2))
    | .add (.add (.mul r2 a) (.mul r b)) c =>
      if arity = 1 && r2 == radix * radix && r == radix then .ok [a,b,c]
      else .error (.unsupportedKey (arity + 2))
    | .add (.mul r addressHead) last =>
      if r == radix then do
        let ps ← keyParts radix bindings (arity + 1) addressHead
        return ps ++ [last]
      else .error (.unsupportedKey (arity + 2))
    | _ => .error (.unsupportedKey (arity + 2))

def rekey (radix arity : Nat) (bindings : List RawAddress) (e : E) : Except Error E :=
  (keyParts radix bindings arity e).map tuple

/-- A raw address universal is exactly a universal over both fresh tuple
components. No finite radix or component bound is assumed. -/
theorem expand_pair_binder (P : Nat → Prop) :
    (∀ key, P key) ↔ ∀ a b, P (cpair a b) := by
  constructor
  · intro h a b; exact h _
  · intro h key
    have hk := h (cun key).1 (cun key).2
    simpa only [cpair_cun] using hk

theorem expand_triple_binder (P : Nat → Prop) :
    (∀ key, P key) ↔ ∀ a b c, P (cpair a (cpair b c)) := by
  constructor
  · intro h a b c; exact h _
  · intro h key
    have hk := h (cun key).1 (cun (cun key).2).1 (cun (cun key).2).2
    simpa only [cpair_cun] using hk

theorem pair_equality (a b c d : Nat) :
    cpair a b = cpair c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have hk := congrArg cun h
    simpa only [cun_cpair, Prod.mk.injEq] using hk
  · rintro ⟨rfl,rfl⟩; rfl

theorem triple_equality (a b c d e f : Nat) :
    cpair a (cpair b c) = cpair d (cpair e f) ↔ a = d ∧ b = e ∧ c = f := by
  rw [pair_equality, pair_equality]

theorem old_radix_collision : 64 * 0 + 64 = 64 * 1 + 0 := by decide +kernel

theorem tuple_collision_refused : cpair 0 64 ≠ cpair 1 0 := by
  intro h
  have h' := (pair_equality 0 64 1 0).mp h
  exact Nat.zero_ne_one h'.1

def expected (r : Except Error E) (e : E) : Bool :=
  match r with | .ok x => beqE x e | .error _ => false

def testResults : List Bool :=
  [expected (rekey 64 2 [] (.add (.mul 64 (.var 1)) (.var 2))) (.tup (.var 1) (.var 2)),
   expected (rekey 64 3 [] (.add (.add (.mul 4096 (.var 1)) (.mul 64 (.var 2))) (.var 3)))
     (.tup (.var 1) (.tup (.var 2) (.var 3))),
   expected (rekey 64 3 [] (.add (.mul 64 (.add (.mul 64 (.var 1)) (.var 2))) (.var 3)))
     (.tup (.var 1) (.tup (.var 2) (.var 3))),
   expected (rekey 64 2 [⟨18,2,[.var 18,.var 101]⟩] (.var 18)) (.tup (.var 18) (.var 101)),
   match rekey 64 2 [] (.var 18) with | .error (.needBinderExpansion 18 2) => true | _ => false,
   match rekey 64 2 [⟨18,2,[.var 18]⟩] (.var 18) with | .error (.malformedBinder 18 2 1) => true | _ => false,
   expected (rekey 64 2 [] (.const 64)) (.tup (.const 1) (.const 0))]

theorem parser_controls : testResults = List.replicate 7 true := by decide +kernel

#print axioms expand_pair_binder
#print axioms expand_triple_binder
#print axioms pair_equality
#print axioms triple_equality
#print axioms old_radix_collision
#print axioms tuple_collision_refused
#print axioms parser_controls
end Bapa.RadixKeySyntax
