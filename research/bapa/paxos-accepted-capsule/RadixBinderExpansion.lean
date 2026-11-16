import RadixKeySyntax
import Sets

/-! A fail-closed, typed binder/instance phase for certificate re-keying.
This phase changes candidate syntax only. It does not claim any certificate is
valid: table columns and arithmetic split/leaf rows still have to be translated
and the complete family checker must accept the result. -/
namespace Bapa.RadixBinderExpansion
open Kern
open RadixKeySyntax

structure Uses where
  outside : Bool := false
  arities : List Nat := []

def Uses.join (a b : Uses) : Uses :=
  ⟨a.outside || b.outside, a.arities ++ b.arities⟩

def mapArity (layouts : List (Nat × Nat)) (mp : Nat) : Option Nat :=
  (layouts.find? (fun p => p.1 == mp)).map (·.2)

mutual
  def inspectE (layouts : List (Nat × Nat)) (v : Nat) : E → Uses
    | .var i => ⟨i == v, []⟩
    | .const _ => {}
    | .get mp (.var i) =>
      if i != v then {} else
        match mapArity layouts mp with
        | some arity => ⟨false,[arity]⟩
        | none => ⟨true,[]⟩
    | .get _ key => inspectE layouts v key
    | .add a b | .sub a b | .min a b | .max a b | .prod a b | .tup a b =>
      (inspectE layouts v a).join (inspectE layouts v b)
    | .mul _ a | .proj _ a => inspectE layouts v a
    | .ite p a b => (inspectC layouts v p).join
      ((inspectE layouts v a).join (inspectE layouts v b))
  def inspectC (layouts : List (Nat × Nat)) (v : Nat) : C → Uses
    | .lt a b | .le a b | .eq a b => (inspectE layouts v a).join (inspectE layouts v b)
    | .and a b | .or a b => (inspectC layouts v a).join (inspectC layouts v b)
    | .not a => inspectC layouts v a
end

structure Expanded where
  candidate : SEntry
  lawAddress : RawAddress
  skolemAddress : RawAddress

/-- Expand a primary universal only if it occurs exclusively as a whole key
of maps sharing an explicit arity. Reusing it as arithmetic, a tuple component,
a different-arity address, or a key of an untyped map is rejected. -/
def expandCandidate (layouts : List (Nat × Nat)) (fresh : List Nat)
    (e : SEntry) : Option Expanded := do
  let v ← e.law.key
  let uses := inspectC layouts v e.law.holds
  let arity ← uses.arities.head?
  if uses.outside || arity < 2 || !(uses.arities.all (· == arity)) ||
      fresh.length + 1 != arity || !(decide fresh.Nodup) ||
      !(fresh.all (fun f => f != v && f != e.sk && !e.keys2.contains f && !occC f e.law.holds)) then
    none
  else
    let parts := E.var v :: fresh.map E.var
    let law' := {e.law with holds := substC [(v,tuple parts)] e.law.holds}
    some ⟨{e with law := law', keys2 := e.keys2 ++ fresh},
      ⟨v,arity,parts⟩, ⟨e.sk,arity,E.var e.sk :: fresh.map E.var⟩⟩

/-- A profile records only those referenced laws whose first binder expanded.
Existing extra arguments are preserved after the new address components. -/
def translatePairInstance (radix : Nat) (profiles : List (Nat × Nat))
    (bindings : List RawAddress) (p : Nat × E × List E) :
    Except Error (Nat × E × List E) := do
  match profiles.find? (fun q => q.1 == p.1) with
  | none => return p
  | some profile =>
    let parts ← keyParts radix bindings profile.2 p.2.1
    match parts with
    | [] => throw (.unsupportedKey profile.2)
    | a :: rest => return (p.1,a,rest ++ p.2.2)

def translateInstances (radix : Nat) (profiles : List (Nat × Nat))
    (bindings : List RawAddress) : List (Nat × E) →
    Except Error (List (Nat × E) × List (Nat × E × List E))
  | [] => .ok ([],[])
  | p :: rest => do
    let (single,multiple) ← translateInstances radix profiles bindings rest
    if (profiles.find? (fun q => q.1 == p.1)).isSome then
      let translated ← translatePairInstance radix profiles bindings (p.1,p.2,[])
      return (single,translated :: multiple)
    else return (p :: single,multiple)

/-- Untyped or mixed-role binders never silently become tuple addresses. -/
theorem mixed_role_refused (layouts : List (Nat × Nat)) (fresh : List Nat)
    (e : SEntry) (v : Nat) (hv : e.law.key = some v)
    (outside : (inspectC layouts v e.law.holds).outside = true) :
    expandCandidate layouts fresh e = none := by
  simp only [expandCandidate, hv, Option.bind_some]
  cases h : (inspectC layouts v e.law.holds).arities.head? with
  | none => simp [h]
  | some n => simp [h, outside]

#print axioms mixed_role_refused
end Bapa.RadixBinderExpansion
