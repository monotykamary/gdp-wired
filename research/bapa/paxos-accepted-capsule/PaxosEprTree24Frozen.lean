import PaxosEprRow12Repair

/-! Candidate-only, syntax-directed tree repairs. No change to the machine,
actual hypotheses, declarations, counts, table, picks or lemmas. Every result
must pass full checkMC. No packed-order equivalence is assumed. -/
namespace Bapa.PaxosEprTree24Frozen
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def scope : List Nat := [7,9,10,13,14,15,16,18,20,23,24]

-- An obsolete bound is removed only for the exact two-row contradiction
-- template and only when its cited actual hypothesis contains erased true.
def contract (tab : List VDef) (hs : List C) : Tree → Tree
 | .split r y n =>
   let erased := match r.coefs, n with
    | [(j,1)], .leafAt [(a,.atom 0),(b,.fact i)] [.input 1,.input 0,.combine 0 1 1 1] [] [] =>
      r.const == -63 && (match tab[j]? with | some (.var _) => true | _ => false) &&
      same a (flip r) && same b r && (match hs[i]? with
       | some h => !((facts tab [] true h).any (same r)) | _ => false)
    | _,_ => false
   if erased then contract tab hs y else .split r (contract tab hs y) (contract tab hs n)
 | t => t

def leafRowsOf : Tree → List (Row × Src)
 | .leaf rs _ _ _ => rs.map (fun r => (r,.any))
 | .leafAt rs _ _ _ | .leafSq rs _ _ _ _ => rs
 | _ => []

def leafEqs : Tree → List (Nat × Nat)
 | .leaf _ _ es _ | .leafAt _ _ es _ | .leafSq _ _ _ es _ => es
 | _ => []

def contradiction (rs : List Row) : Option Tree := do
 if let some r := rs.find? (fun r => allZero r.coefs && r.const > 0) then
   return .leafAt [(r,.any)] [.input 0] [] []
 rs.findSome? fun a => rs.findSome? fun b =>
  if allZero (ladd a b).coefs && (ladd a b).const > 0 then
   some (.leafAt [(a,.any),(b,.any)] [.input 0,.input 1,.combine 0 1 1 1] [] [])
  else none

-- Eliminate only equal coordinates for which BOTH zero-difference rows are
-- literally present. The generated proof is a sum of those available rows.
def equalities (rs : List Row) : List (Nat × Nat) := rs.filterMap fun r =>
 match r.coefs with
 | [(i,1),(j,-1)] =>
   if r.const == 0 && i < j && rs.any (same (lscale (-1) r)) then some (i,j) else none
 | _ => none

def cancelEqual (eqs : List (Nat × Nat)) (r : Row) : Row × List (Row × Int) :=
 eqs.foldr (fun (i,j) (a,used) =>
   let c := (a.coefs.find? (fun p => p.1 == j)).map (·.2) |>.getD 0
   if c == 0 then (a,used) else
   let e : Row := if c > 0 then ⟨[(i,1),(j,-1)],0⟩ else ⟨[(i,-1),(j,1)],0⟩
   (ladd a (lscale c.natAbs e), used ++ [(e,Int.ofNat c.natAbs)])) (r,[])

def equalityContradiction (rs : List Row) : Option Tree :=
 rs.findSome? fun r =>
  let (endRow,used) := cancelEqual (equalities rs) r
  if !(allZero endRow.coefs && endRow.const > 0) then none else
  let inputs := r :: used.map (·.1)
  let steps := used.zipIdx.foldl (fun ss (p,i) =>
    ss ++ [.input (i+1), .combine (2*i) (2*i+1) 1 p.2]) [.input 0]
  some (.leafAt (inputs.map (fun a => (a,.any))) steps [] [])

-- Return the first unresolved atomic test in the actual cited syntax. Tuple
-- equality is expanded coordinate by coordinate, never via packed order.
mutual
 def testE (tab : List VDef) (p : Path) : E → Option Row
  | .ite c a b => match truth tab p c with
    | some true => testE tab p a
    | some false => testE tab p b
    | none => testC tab p c
  | .add a b | .sub a b | .min a b | .max a b | .prod a b | .tup a b => testE tab p a |>.orElse (fun _ => testE tab p b)
  | .mul _ a | .get _ a | .proj _ a => testE tab p a
  | _ => none
 def testC (tab : List VDef) (p : Path) : C → Option Row
  | .not a => testC tab p a
  | .and a b | .or a b =>
    (if truth tab p a == none then testC tab p a else none) |>.orElse
     (fun _ => if truth tab p b == none then testC tab p b else none)
  | c@(.eq a b) =>
    (testE tab p a).orElse (fun _ => testE tab p b) |>.orElse (fun _ =>
     if truth tab p c != none then none else
     if isTup a && isTup b then do
      let xs ← parts tab p a
      let ys ← parts tab p b
      (xs.zip ys).findSome? fun (x,y) =>
       let r := lsub x y
       if dec p r == none then some r else
       if dec p (lscale (-1) r) == none then some (lscale (-1) r) else none
     else do
      let x ← linear tab p a
      let y ← linear tab p b
      let r := lsub x y
      if dec p r == none then some r else
      if dec p (lscale (-1) r) == none then some (lscale (-1) r) else none)
  | c@(.le a b) | c@(.lt a b) =>
    (testE tab p a).orElse (fun _ => testE tab p b) |>.orElse (fun _ => do
     if truth tab p c != none then none else do
      let x ← linear tab p a
      let y ← linear tab p b
      return match c with | .lt _ _ => ladd (lsub x y) (lconst 1) | _ => lsub x y)
end

def missingTest (tab : List VDef) (hs : List C) (p : Path) (t : Tree) : Option Row :=
 let avail := leafRows tab p hs (leafEqs t)
 (leafRowsOf t).findSome? fun (r,src) =>
  if avail.any (same r) then none else match src with
  | .fact i => hs[i]?.bind (testC tab p)
  | .term i => match tab[i]? with | some (.term e) => testE tab p e | _ => none
  | .eq i => do
    let (a,b) ← (leafEqs t)[i]?
    let some (.cellT m xs) := tab[a]? | none
    let some (.cellT n ys) := tab[b]? | none
    if m != n || xs.length != ys.length then none else
     (xs.zip ys).findSome? fun (x,y) =>
      let r := lsub x y
      if dec p r == none then some r else
      if dec p (lscale (-1) r) == none then some (lscale (-1) r) else none
  | _ => none

def repairLeaf (tab : List VDef) (hs : List C) : Nat → Path → Tree → Tree
 | 0,_,t => t
 | fuel+1,p,t =>
   if checkT tab hs p t then t else
   let rs := p.map atomRow ++ (leafRowsOf t).flatMap (fun (_,s) => srcRows tab p hs (leafEqs t) s)
   match (contradiction rs).orElse (fun _ => equalityContradiction rs) with
   | some proof => proof
   | none => match missingTest tab hs p t with
     | none => t
     | some r => .split r (repairLeaf tab hs fuel ((r,true)::p) t)
                         (repairLeaf tab hs fuel ((r,false)::p) t)

def walk (fuel : Nat) (tab : List VDef) (hs : List C) (lemmas : List CutLemma) (p : Path) : Tree → Tree
 | .split r y n => .split r (walk fuel tab hs lemmas ((r,true)::p) y) (walk fuel tab hs lemmas ((r,false)::p) n)
 | t => repairLeaf tab hs fuel (lemmaPath lemmas p) t

-- Cell congruence needs the same typed equality plan even when no ITE in
-- the goal mentions that pair of keys. Recognize full keys and suffixes,
-- retaining the exact equality/identical-unequal-continuation guard.
def addressPlan (tab : List VDef) (r : Row) : Option (List Row) :=
 let cells := tab.filterMap (fun d => match d with | .cellT m rs => some (m,rs) | _ => none)
 cells.findSome? fun (m,xs) => cells.findSome? fun (n,ys) =>
  if m != n || xs.length != ys.length then none else
  (List.range xs.length).findSome? fun off =>
   let a := xs.drop off
   let b := ys.drop off
   let packed := lsub (PaxosEprTreeRepair.packedRows a) (PaxosEprTreeRepair.packedRows b)
   if same r packed || same r (lscale (-1) packed) then
    some ((a.zip b).map fun (x,y) => lsub x y)
   else none

def typedPlan (tab : List VDef) (hs : List C) (r : Row) : Option (List Row) :=
 (PaxosEprTypedEqualityTree.plan tab hs r).orElse (fun _ => addressPlan tab r)

def typedNode (tab : List VDef) (hs : List C) (r : Row) (y n : Tree) : Tree :=
 match n with
 | .split s ny nn =>
   if same s (ladd (lscale (-1) r) (lconst 2)) &&
      decide (PaxosEprTypedEqualityTree.hintless y = PaxosEprTypedEqualityTree.hintless ny) then
    match typedPlan tab hs (ladd r (lconst (-1))) with
    | some rs => PaxosEprTreeRepair.equalityCases nn (PaxosEprTypedEqualityTree.hintless y) rs
    | none => .split r y n
   else .split r y n
 | _ => match y with
   | .split s yy yn =>
     if same s (lscale (-1) r) &&
        decide (PaxosEprTypedEqualityTree.hintless yn = PaxosEprTypedEqualityTree.hintless n) then
      match typedPlan tab hs r with
      | some rs => PaxosEprTreeRepair.equalityCases yy (PaxosEprTypedEqualityTree.hintless n) rs
      | none => .split r y n
     else .split r y n
   | _ => .split r y n

-- Remaining packed-order decisions are only candidate proof structure.
-- Retarget them to their leading typed coordinate; the checker validates
-- both new branches, with no claim of equivalence to packed ordering.
def projectRow (tab : List VDef) (r : Row) : Row := Id.run do
 if r.const != 0 && r.const != 1 then return r
 let base := {r with const := 0}
 let some rs := addressPlan tab base | return r
 let some head := rs.find? (fun a => !allZero a.coefs) | return r
 let packed := PaxosEprTreeRepair.packedRows rs
 let head := if same base packed then head else lscale (-1) head
 return {head with const := r.const}

def typedTransform (tab : List VDef) (hs : List C) : Tree → Tree
 | .split r y n => typedNode tab hs (PaxosEprTypedEqualityTree.primitiveSplit r)
   (typedTransform tab hs y) (typedTransform tab hs n)
 | t => t

def projectTree (tab : List VDef) : Tree → Tree
 | .split r y n => .split (projectRow tab r) (projectTree tab y) (projectTree tab n)
 | .leaf rs ss es ps =>
   let rs' := rs.map (fun r => PaxosEprTypedEqualityTree.primitiveSplit (projectRow tab r))
   .leaf rs' (PaxosEprRow12Repair.adaptSteps rs' ss 0 []) es ps
 | .leafAt rs ss es ps =>
   let rs' := rs.map (fun (r,s) => (PaxosEprTypedEqualityTree.primitiveSplit (projectRow tab r),s))
   .leafAt rs' (PaxosEprRow12Repair.adaptSteps (rs'.map (·.1)) ss 0 []) es ps
 | t => t

def repairTree (i : Nat) (goal : List C) (ds : List CDecl) (k : CCert) : Except String Tree := do
 if !scope.contains i || !(namedIn goal k.hyps goal) then throw "outside eleven exact STEP contexts"
 let some hs := PaxosEprTreeRepair.context ds k | throw "count context unavailable"
 let t := contract k.tab hs k.tree
 let t := typedTransform k.tab k.hyps t
 let t := projectTree k.tab t
 let t := walk (if i == 7 then 4 else 8) k.tab hs k.lemmas [] t
 return PaxosEprTreeRepair.closeConstants k.tab hs k.lemmas [] t

def repair (i : Nat) (goal : List C) (ds : List CDecl) (k : CCert) : Except String CCert :=
 (repairTree i goal ds k).map (fun t => {k with tree := t})

theorem non_tree_fields_preserved (i : Nat) (goal : List C) (ds : List CDecl)
 (k k' : CCert) (h : repair i goal ds k = .ok k') :
 k'.hyps = k.hyps ∧ k'.reads = k.reads ∧ k'.insts = k.insts ∧
 k'.tab = k.tab ∧ k'.picks = k.picks ∧ k'.lemmas = k.lemmas := by
 cases he : repairTree i goal ds k with
 | error e => simp [repair, he, Except.map] at h
 | ok t =>
   simp [repair, he, Except.map] at h
   subst k'
   exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms non_tree_fields_preserved
end Bapa.PaxosEprTree24Frozen
