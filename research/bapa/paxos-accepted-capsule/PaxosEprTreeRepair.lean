import CountMachine

/-! Family-local candidate repair only. Every result requires full checkMC.
No goal, declaration, named hypothesis, count read, witness or table is changed.
Packed order is never interpreted as tuple order. -/
namespace Bapa.PaxosEprTreeRepair
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

deriving instance DecidableEq for Cert.Row, Cert.Step, Kern.Src, Kern.Tree

def context (ds : List CDecl) (k : CCert) : Option (List C) := do
 let cs ← toCounts ds k.reads
 let hs ← countHyps cs k.insts
 return k.hyps ++ k.reads.map (readHyp ds) ++ pickHyps ds k.reads k.picks ++ hs

def packedRows : List Cert.Row → Cert.Row
 | [] => lconst 0
 | r::rs => ladd (lscale (Int.ofNat (64^rs.length)) r) (packedRows rs)

def tupleComponents (tab : List VDef) (r : Cert.Row) : Option (List Cert.Row) :=
 tab.findSome? fun d => match d with
 | .term (.ite (.eq a b) _ _) => do
   if !(isTup a && isTup b) then none else do
    let xs ← parts tab [] a
    let ys ← parts tab [] b
    if xs.length != ys.length then none else do
     let packed := lsub (packedRows xs) (packedRows ys)
     if same r packed || same r (lscale (-1) packed) then
       some ((xs.zip ys).map fun p => lsub p.1 p.2)
     else none
 | _ => none

-- The unequal continuation is shared. No ordering correspondence is asserted.
def equalityCases (yes no : Tree) : List Cert.Row → Tree
 | [] => yes
 | r::rs =>
   if allZero r.coefs then
     if r.const == 0 then equalityCases yes no rs else no
   else .split r (.split (lscale (-1) r) (equalityCases yes no rs) no) no

def tupleRoot (k : CCert) : Except String Tree :=
 match k.tree with
 | .split r (.split s yy yn) n =>
   if !(same s (lscale (-1) r)) || !(decide (yn = n)) then
     .error "root is not an equality with identical unequal continuations"
   else match tupleComponents k.tab r with
    | none => .error "no exact typed tuple-ITE root plan"
    | some rs => .ok (equalityCases yy n rs)
 | _ => .error "unexpected kind-law root"

def hasTrueConj (c : C) : Bool :=
 beqC c trueC || (match c with | .and a b => hasTrueConj a || hasTrueConj b | _ => false)

-- Only the retained value bounds in steps19/22, and only the exact stale
-- two-row contradiction template. Promoting y removes the bound assumption;
-- no true path atom is injected. This is a candidate, not a validity theorem.
def erasedValueBound (tab : List VDef) (hs : List C) (r : Cert.Row) (n : Tree) : Bool :=
 let shaped := match r.coefs with
  | [(j,a)] => a == 1 && r.const == -63 && (match tab[j]? with
      | some (.var v) => v == 5 || v == 12 | _ => false)
  | _ => false
 shaped && (match n with
  | .leafAt [(a,.atom 0),(b,.fact i)] [.input 1,.input 0,.combine 0 1 1 1] [] [] =>
    same a (flip r) && same b r && (match hs[i]? with | some h => hasTrueConj h | _ => false)
  | _ => false)

def contractBounds (tab : List VDef) (hs : List C) : Tree → Tree
 | .split r y n =>
   if erasedValueBound tab hs r n then contractBounds tab hs y
   else .split r (contractBounds tab hs y) (contractBounds tab hs n)
 | t => t

def constantFact (tab : List VDef) (hs : List C) (p : Path) : Option Tree :=
 hs.zipIdx.findSome? fun (h,i) =>
   ((facts tab p true h).find? (fun r => allZero r.coefs && r.const > 0)).map fun r =>
     .leafAt [(r,.fact i)] [.input 0] [] []

-- Direct lookup of an already available positive constant, not arithmetic
-- search, and never use an isolated subcondition as a whole hypothesis.
def closeConstants (tab : List VDef) (hs : List C) (lemmas : List CutLemma) (p : Path) : Tree → Tree
 | .split r y n => .split r (closeConstants tab hs lemmas ((r,true)::p) y) (closeConstants tab hs lemmas ((r,false)::p) n)
 | t => (constantFact tab hs (lemmaPath lemmas p)).getD t

def repairTree (lawId : Nat) (goal : List C) (ds : List CDecl) (k : CCert) : Except String Tree := do
 if !(namedIn goal k.hyps goal) then throw "named hypotheses not in exact goal"
 let some hs := context ds k | throw "count context unavailable"
 if lawId == 4 || lawId == 5 then tupleRoot k
 else if lawId == 19 || lawId == 22 then
   return closeConstants k.tab hs k.lemmas [] (contractBounds k.tab hs k.tree)
 else if lawId == 21 then return closeConstants k.tab hs k.lemmas [] k.tree
 else throw "outside exclusive tree-five scope"

def repair (lawId : Nat) (goal : List C) (ds : List CDecl) (k : CCert) : Except String CCert :=
 (repairTree lawId goal ds k).map (fun t => {k with tree := t})

theorem non_tree_fields_preserved (lawId : Nat) (goal : List C) (ds : List CDecl)
 (k k' : CCert) (h : repair lawId goal ds k = .ok k') :
 k'.hyps = k.hyps ∧ k'.reads = k.reads ∧ k'.insts = k.insts ∧
 k'.tab = k.tab ∧ k'.picks = k.picks ∧ k'.lemmas = k.lemmas := by
 cases he : repairTree lawId goal ds k with
 | error e => simp [repair, he, Except.map] at h
 | ok t =>
   simp [repair, he, Except.map] at h
   subst k'
   exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms non_tree_fields_preserved
end Bapa.PaxosEprTreeRepair
