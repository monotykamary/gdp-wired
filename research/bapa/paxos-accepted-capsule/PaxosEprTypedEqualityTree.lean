import PaxosEprTreeRepair
namespace Bapa.PaxosEprTypedEqualityTree
open Kern Cert
/-! Source hints are optional (leafAtOk checks the complete available rows as
fallback). Canonicalizing hints changes no required row or arithmetic step.
Only equality trichotomies with identical unequal proofs after that hint
canonicalization may be replaced. Never interpret packed order as tuple order. -/
def hintless : Tree → Tree
 | .split r y n => .split r (hintless y) (hintless n)
 | .leaf rs ss es ps => .leaf rs ss es ps
 | .leafAt rs ss es ps => .leafAt (rs.map (fun p => (p.1,Src.any))) ss es ps
 | .leafSq rs sqs ss es ps => .leafSq (rs.map (fun p => (p.1,Src.any))) sqs ss es ps

mutual
 def termsE : E → List E
  | e@(.ite c a b) => e :: (termsC c ++ termsE a ++ termsE b)
  | .add a b | .sub a b | .min a b | .max a b | .prod a b | .tup a b => termsE a ++ termsE b
  | .mul _ a | .get _ a | .proj _ a => termsE a
  | _ => []
 def termsC : C → List E
  | .lt a b | .le a b | .eq a b => termsE a ++ termsE b
  | .and a b | .or a b => termsC a ++ termsC b
  | .not a => termsC a
end

/-- The actual named hypotheses contain post-state choices that need not have
whole-term table columns. Components are still resolved ONLY in the real table. -/
def plan (tab : List VDef) (hs : List C) (r : Row) : Option (List Row) :=
 ((hs.flatMap termsC) ++ tab.filterMap (fun d => match d with | .term e => some e | _ => none)).findSome? fun e =>
  match e with
  | .ite (.eq a b) _ _ => do
    if !(isTup a && isTup b) then none else do
     let xs ← parts tab [] a
     let ys ← parts tab [] b
     if xs.length != ys.length then none else do
      let p := lsub (PaxosEprTreeRepair.packedRows xs) (PaxosEprTreeRepair.packedRows ys)
      if same r p || same r (lscale (-1) p) then some ((xs.zip ys).map fun p => lsub p.1 p.2) else none
  | _ => none

def node (tab : List VDef) (hs : List C) (r : Row) (y n : Tree) : Tree :=
 match n with
 | .split s ny nn =>
   if same s (ladd (lscale (-1) r) (lconst 2)) && decide (hintless y = hintless ny) then
    match plan tab hs (ladd r (lconst (-1))) with
    | some rs => PaxosEprTreeRepair.equalityCases nn (hintless y) rs
    | none => .split r y n
   else .split r y n
 | _ => match y with
   | .split s yy yn =>
     if same s (lscale (-1) r) && decide (hintless yn = hintless n) then
      match plan tab hs r with
      | some rs => PaxosEprTreeRepair.equalityCases yy (hintless n) rs
      | none => .split r y n
     else .split r y n
   | _ => .split r y n

/-- Strict comparison of a single scaled coordinate difference. Dividing its
positive common scale with integer rounding exposes ordinary scalar equality;
this is not a packed-key order conversion. Child proofs still need checkMC. -/
def primitiveSplit (r : Row) : Row :=
 match r.coefs with
 | [(i,a),(j,b)] =>
   let scale := if a == 4096 || a == -4096 then 4096 else if a == 64 || a == -64 then 64 else 0
   if scale != 0 && b == -a && (r.const == 0 || r.const == 1) then ⟨[(i,a/scale),(j,b/scale)],r.const⟩ else r
 | _ => r

def transform (tab : List VDef) (hs : List C) : Tree → Tree
 | .split r y n => node tab hs (primitiveSplit r) (transform tab hs y) (transform tab hs n)
 | t => t
end Bapa.PaxosEprTypedEqualityTree
