import PaxosEprTreeRepair
namespace Bapa.PaxosEprKindRepair
open Kern
/-! Candidate repair only. Projection normalization is a recognizer for the
exact table slot's goal origin, not a replacement of any goal/hypothesis. -/
mutual
 def normalE : E → E
  | .var n => .var n | .const n => .const n
  | .add a b => .add (normalE a) (normalE b)
  | .sub a b => .sub (normalE a) (normalE b)
  | .mul n a => .mul n (normalE a)
  | .prod a b => .prod (normalE a) (normalE b)
  | .min a b => .min (normalE a) (normalE b)
  | .max a b => .max (normalE a) (normalE b)
  | .get m a => .get m (normalE a)
  | .tup a b => .tup (normalE a) (normalE b)
  | .ite c a b => .ite (normalC c) (normalE a) (normalE b)
  | .proj i a => match normalE a with
    | .tup l r => if i == 0 then l else if i == 1 then r else .proj i (.tup l r)
    | a => .proj i a
 def normalC : C → C
  | .lt a b => .lt (normalE a) (normalE b)
  | .le a b => .le (normalE a) (normalE b)
  | .eq a b => .eq (normalE a) (normalE b)
  | .and a b => .and (normalC a) (normalC b)
  | .or a b => .or (normalC a) (normalC b)
  | .not a => .not (normalC a)
end

def repair (i : Nat) (goal : List C) (k : CCert) : Except String CCert := do
 if !(namedIn goal k.hyps goal) then throw "named hypotheses unavailable"
 if i == 1 || i == 3 then
   let t ← PaxosEprTreeRepair.tupleRoot k
   return {k with tree := t}
 else if i == 2 then
   match (k.hyps[24]? : Option C), (k.tab[145]? : Option VDef) with
   | some (.not (.le e (.const 1))), some (.term old) =>
     if beqE (normalE e) old then return {k with tab := k.tab.set 145 (.term e)}
     else throw "exact projected goal origin does not match normalized slot145"
   | _, _ => throw "unexpected law2 term/hypothesis shape"
 else throw "outside remaining kind-law scope"
end Bapa.PaxosEprKindRepair
