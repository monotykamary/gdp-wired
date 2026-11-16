import PaxosEprTypedEqualityTree
namespace Bapa.PaxosEprRow12Repair
open Kern Cert
/-! Retarget only the four exact retained block-bound row shapes for the
registered (round29,value2000002) witness. This is a candidate transformation,
not a packed-order theorem. Full checkMC must validate every transformed row,
path and unchanged arithmetic derivation. No low-coordinate bound is added. -/
def row (r : Row) : Row := Id.run do
 let some low := r.coefs.find? (fun p => p.1 == 10) | return r
 let some high := r.coefs.find? (fun p => p.1 == 40) | return r
 if high.2 != 64 * low.2 then return r
 let rest := r.coefs.filter (fun p => p.1 != 10)
 if !(rest.all (fun p => p.2 % 64 == 0)) then return r
 let c : Option Int :=
  if low.2 == 1 && r.const == 1 then some 1
  else if low.2 == 1 && r.const == -63 then some 0
  else if low.2 == -1 && r.const == 0 then some 0
  else if low.2 == -1 && r.const == 64 then some 1
  else none
 let some c := c | return r
 return ⟨rest.map (fun p => (p.1,p.2 / 64)),c⟩

/-- A previously scaled cut becomes an identity cut only when its actual
replayed input validates the same output with g=1. No new row is invented. -/
def adaptSteps (inputs : List Row) : List Step → Nat → List Row → List Step
 | [],_,_ => []
 | s::ss,n,rows =>
   let s' := match s with
    | .cut o g q c =>
      match rows[n-1-o]? with
      | some a => if o < n && (g == 64 || g == 4096) && !(cutOk a g q c) && cutOk a 1 q c
        then .cut o 1 q c else s
      | none => s
    | _ => s
   match replay inputs [s'] n rows with
   | some out => s' :: adaptSteps inputs ss (n+1) out
   | none => s :: ss

def tree : Tree → Tree
 | .split r y n => .split (row r) (tree y) (tree n)
 | .leaf rs ss es ps =>
   let rs' := rs.map (fun r => PaxosEprTypedEqualityTree.primitiveSplit (row r))
   .leaf rs' (adaptSteps rs' ss 0 []) es ps
 | .leafAt rs ss es ps =>
   let rs' := rs.map (fun p => (PaxosEprTypedEqualityTree.primitiveSplit (row p.1),p.2))
   .leafAt rs' (adaptSteps (rs'.map (·.1)) ss 0 []) es ps
 | .leafSq rs sqs ss es ps => .leafSq (rs.map (fun p => (PaxosEprTypedEqualityTree.primitiveSplit (row p.1),p.2))) sqs ss es ps

def applyRows (k : CCert) : CCert := {k with tree := PaxosEprTypedEqualityTree.transform k.tab k.hyps (tree k.tree)}

def repair (i : Nat) (goal : List C) (k : CCert) : Except String CCert := do
 if i != 12 || !(namedIn goal k.hyps goal) then throw "outside exact law12 context"
 match (k.tab[10]? : Option VDef), (k.tab[40]? : Option VDef) with
 | some (.var 2000002), some (.var 29) => return applyRows k
 | _, _ => throw "registered scalar/witness columns differ"

theorem non_tree_fields_preserved (k : CCert) :
 (applyRows k).hyps = k.hyps ∧ (applyRows k).reads = k.reads ∧
 (applyRows k).insts = k.insts ∧ (applyRows k).tab = k.tab ∧
 (applyRows k).picks = k.picks ∧ (applyRows k).lemmas = k.lemmas :=
 ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms non_tree_fields_preserved
end Bapa.PaxosEprRow12Repair
