import CertificateBoundErasure

/-! Search-free bound substitution, not erasure. A fresh, fixed parameter is
inserted as column0. All old column references shift by one. The retained tree
and arithmetic steps remain, with recognized literal bound rows translated from
x<bound to x<size. Only a complete post-translation check can accept the result. -/
namespace Bapa.CertificateBoundSubstitution
open Kern

mutual
  def expr (bound size : Nat) : E → E
    | .var i => .var i
    | .const n => .const n
    | .add a b => .add (expr bound size a) (expr bound size b)
    | .sub a b => .sub (expr bound size a) (expr bound size b)
    | .mul n a => .mul n (expr bound size a)
    | .min a b => .min (expr bound size a) (expr bound size b)
    | .max a b => .max (expr bound size a) (expr bound size b)
    | .prod a b => .prod (expr bound size a) (expr bound size b)
    | .ite p a b => .ite (condition bound size p) (expr bound size a) (expr bound size b)
    | .get m k => .get m (expr bound size k)
    | .tup a b => .tup (expr bound size a) (expr bound size b)
    | .proj i a => .proj i (expr bound size a)
  def condition (bound size : Nat) : C → C
    | .lt a (.const n) => .lt (expr bound size a) (if n = bound then .var size else .const n)
    | .le a (.const n) => .le (expr bound size a) (if n = bound then .var size else .const n)
    | .lt a b => .lt (expr bound size a) (expr bound size b)
    | .le a b => .le (expr bound size a) (expr bound size b)
    | .eq a b => .eq (expr bound size a) (expr bound size b)
    | .and a b => .and (condition bound size a) (condition bound size b)
    | .or a b => .or (condition bound size a) (condition bound size b)
    | .not a => .not (condition bound size a)
end

def shiftRow (r : Cert.Row) : Cert.Row :=
  ⟨r.coefs.map (fun (i,c) => (i+1,c)),r.const⟩

/-- Replace only the four literal, one-column bound/complement patterns. -/
def boundRow (bound : Nat) (r : Cert.Row) : Cert.Row :=
  let shifted := shiftRow r
  match r.coefs with
  | [(_,a)] =>
    if a == 1 && r.const == 1 - (bound : Int) then ⟨(0,-1)::shifted.coefs,1⟩
    else if a == 1 && r.const == -(bound : Int) then ⟨(0,-1)::shifted.coefs,0⟩
    else if a == (-1) && r.const == (bound : Int) then ⟨(0,1)::shifted.coefs,0⟩
    else if a == (-1) && r.const == (bound : Int)+1 then ⟨(0,1)::shifted.coefs,1⟩
    else shifted
  | _ => shifted

def source : Src → Src
  | .nat i => .nat (i+1)
  | .term i => .term (i+1)
  | s => s

def proofStep (bound : Nat) : Cert.Step → Cert.Step
  | .cut i g q c => let r := boundRow bound ⟨q,c⟩; .cut i g r.coefs r.const
  | s => s

def eqPairs (pairs : List (Nat × Nat)) : List (Nat × Nat) :=
  pairs.map (fun (i,j) => (i+1,j+1))

def tree (bound : Nat) : Tree → Tree
  | .split r a b => .split (boundRow bound r) (tree bound a) (tree bound b)
  | .leaf rs ss eqs prods =>
    .leaf (rs.map (boundRow bound)) (ss.map (proofStep bound)) (eqPairs eqs) prods
  | .leafAt rs ss eqs prods =>
    .leafAt (rs.map (fun (r,s) => (boundRow bound r,source s)))
      (ss.map (proofStep bound)) (eqPairs eqs) prods
  | .leafSq rs sqs ss eqs prods =>
    .leafSq (rs.map (fun (r,s) => (boundRow bound r,source s)))
      (sqs.map shiftRow) (ss.map (proofStep bound)) (eqPairs eqs) prods

def variableDefinition (bound size : Nat) : VDef → VDef
  | .var i => .var i
  | .cell m key => .cell m (shiftRow key)
  | .cellT m keys => .cellT m (keys.map shiftRow)
  | .mono fs => .mono (fs.map (·+1))
  | .term e => .term (expr bound size e)

def certificate (bound size : Nat) (k : Kern.Cert) : Kern.Cert :=
  (.var size :: k.1.map (variableDefinition bound size),
   k.2.1.map (condition bound size),tree bound k.2.2)

def law (bound size : Nat) (l : MLaw) : MLaw :=
  {l with holds := condition bound size l.holds}

def scalarMachine (bound size : Nat) (m : MMachine) : MMachine :=
  {m with
    init := m.init.map (fun p => (p.1,expr bound size p.2))
    step := m.step.map (fun p => (p.1,expr bound size p.2))
    writes := m.writes.map (fun p => (p.1,expr bound size p.2.1,expr bound size p.2.2))
    pre := condition bound size m.pre
    assume := condition bound size m.assume}

def pairInstances (bound size : Nat) (ps : List (Nat × E × List E)) : List (Nat × E × List E) :=
  ps.map (fun p => (p.1,expr bound size p.2.1,p.2.2.map (expr bound size)))

def machine (bound size : Nat) (s : SMachine) : SMachine :=
  {s with
    f := {s.f with
      m := scalarMachine bound size s.f.m
      flags := s.f.flags.map (fun p => (p.1,condition bound size p.2))}
    every := s.every.map (fun p => (p.1,p.2.1,expr bound size p.2.2))
    qflags := s.qflags.map (fun p => (p.1,p.2.1,condition bound size p.2.2))
    facts := s.facts.map (law bound size)
    pfacts := s.pfacts.map (fun p => (law bound size p.1,p.2))}

def entry (bound size : Nat) (e : SEntry) : SEntry :=
  {e with
    law := law bound size e.law
    insts := e.insts.map (fun p => (p.1,expr bound size p.2))
    qinsts := e.qinsts.map (fun p => (p.1,p.2.map (expr bound size)))
    finsts := e.finsts.map (fun p => (p.1,expr bound size p.2))
    pinsts := pairInstances bound size e.pinsts
    pfinsts := pairInstances bound size e.pfinsts
    start := certificate bound size e.start
    step := certificate bound size e.step}

theorem size_column (bound size : Nat) (k : Kern.Cert) :
    (certificate bound size k).1.head? = some (.var size) := rfl

theorem strict_bound_pattern :
    (boundRow 64 (sp [(2,1)] (-63))).coefs = [(0,-1),(3,1)] ∧
    (boundRow 64 (sp [(2,1)] (-63))).const = 1 := by decide +kernel

theorem complement_pattern :
    (boundRow 64 (sp [(48,-1)] 64)).coefs = [(0,1),(49,-1)] ∧
    (boundRow 64 (sp [(48,-1)] 64)).const = 0 := by decide +kernel

theorem checked_transport (bound size : Nat) (s : SMachine) (ps : List SEntry)
    (h : checkSMachine (machine bound size s) (ps.map (entry bound size)) = true) :
    ∀ ρ M, SReach (machine bound size s) ρ M → ∀ e ∈ ps.map (entry bound size), e.Holds ρ M :=
  smachine_sound _ _ h

#print axioms size_column
#print axioms strict_bound_pattern
#print axioms complement_pattern
#print axioms checked_transport
end Bapa.CertificateBoundSubstitution

/-! Per-sort variant. Typings are untrusted annotations: missing/ambiguous
annotations refuse emission, and every translated certificate must recheck.
A typing is local to one entry, because bound names can have different roles
in different laws. Parameter numbers denote fresh fixed environment variables.
The legacy common-size API above is deliberately unchanged. -/
namespace Bapa.CertificateBoundSubstitution.Typed
open Kern

structure Typing where
  sizes : List Nat
  variables : List (Nat × Nat)
  values : List (Nat × Nat)

def lookupSize (xs : List (Nat × Nat)) (i : Nat) : Option Nat :=
  (xs.find? (fun p => p.1 == i)).map (·.2)

def exprSize (p : Typing) : E → Option Nat
  | .var i => lookupSize p.variables i
  | .get m _ => lookupSize p.values m
  | .ite _ a b => match a, b with
    | .const _, _ => exprSize p b
    | _, .const _ => exprSize p a
    | _, _ => let x := exprSize p a; if x == exprSize p b then x else none
  | .add a (.const _) | .sub a (.const _) => exprSize p a
  | _ => none

def sizeOf (p : Typing) (e : E) : Option Nat := do
  let n ← exprSize p e
  if p.sizes.contains n then some n else none

mutual
  def expr (bound : Nat) (p : Typing) : E → Option E
    | .var i => some (.var i)
    | .const n => some (.const n)
    | .add a b => do return .add (← expr bound p a) (← expr bound p b)
    | .sub a b => do return .sub (← expr bound p a) (← expr bound p b)
    | .mul n a => do return .mul n (← expr bound p a)
    | .min a b => do return .min (← expr bound p a) (← expr bound p b)
    | .max a b => do return .max (← expr bound p a) (← expr bound p b)
    | .prod a b => do return .prod (← expr bound p a) (← expr bound p b)
    | .ite c a b => do return .ite (← condition bound p c) (← expr bound p a) (← expr bound p b)
    | .get m k => do return .get m (← expr bound p k)
    | .tup a b => do return .tup (← expr bound p a) (← expr bound p b)
    | .proj i a => do return .proj i (← expr bound p a)
  def condition (bound : Nat) (p : Typing) : C → Option C
    | .lt a (.const n) => do
      let a' ← expr bound p a
      if n == bound then return .lt a' (.var (← sizeOf p a)) else return .lt a' (.const n)
    | .le a (.const n) => do
      let a' ← expr bound p a
      if n == bound then return .le a' (.var (← sizeOf p a)) else return .le a' (.const n)
    | .lt a b => do return .lt (← expr bound p a) (← expr bound p b)
    | .le a b => do return .le (← expr bound p a) (← expr bound p b)
    | .eq a b => do return .eq (← expr bound p a) (← expr bound p b)
    | .and a b => do return .and (← condition bound p a) (← condition bound p b)
    | .or a b => do return .or (← condition bound p a) (← condition bound p b)
    | .not a => do return .not (← condition bound p a)
end

def shiftRow (n : Nat) (r : Cert.Row) : Cert.Row :=
  ⟨r.coefs.map (fun (i,c) => (i+n,c)),r.const⟩

def columnSize (p : Typing) (tab : List VDef) (i : Nat) : Option Nat := do
  let v ← tab[i]?
  let n ← match v with
    | .var x => lookupSize p.variables x
    | .cell m _ | .cellT m _ => lookupSize p.values m
    | .term e => exprSize p e
    | .mono _ => none
  if p.sizes.contains n then some (p.sizes.idxOf n) else none

/-- Only the four old bound/complement row patterns change besides the uniform
column shift. A recognized bound on an untyped column is an explicit refusal. -/
def boundRow (bound : Nat) (p : Typing) (tab : List VDef) (r : Cert.Row) : Option Cert.Row := do
  let shifted := shiftRow p.sizes.length r
  match r.coefs with
  | [(i,a)] =>
    if a == 1 && r.const == 1 - (bound : Int) then
      return ⟨((← columnSize p tab i),-1)::shifted.coefs,1⟩
    else if a == 1 && r.const == -(bound : Int) then
      return ⟨((← columnSize p tab i),-1)::shifted.coefs,0⟩
    else if a == (-1) && r.const == (bound : Int) then
      return ⟨((← columnSize p tab i),1)::shifted.coefs,0⟩
    else if a == (-1) && r.const == (bound : Int)+1 then
      return ⟨((← columnSize p tab i),1)::shifted.coefs,1⟩
    else return shifted
  | _ => do return shifted

def source (n : Nat) : Src → Src
  | .nat i => .nat (i+n)
  | .term i => .term (i+n)
  | s => s

def proofStep (bound : Nat) (p : Typing) (tab : List VDef) : Cert.Step → Option Cert.Step
  | .cut i g q c => do
    let r ← boundRow bound p tab ⟨q,c⟩
    return .cut i g r.coefs r.const
  | s => some s

def eqPairs (n : Nat) (pairs : List (Nat × Nat)) : List (Nat × Nat) :=
  pairs.map (fun (i,j) => (i+n,j+n))

def tree (bound : Nat) (p : Typing) (tab : List VDef) : Tree → Option Tree
  | .split r a b => do
    let r' ← boundRow bound p tab r
    let a' ← tree bound p tab a
    let b' ← tree bound p tab b
    return .split r' a' b'
  | .leaf rs ss eqs prods => do
    let rs' ← rs.mapM (boundRow bound p tab)
    let ss' ← ss.mapM (proofStep bound p tab)
    return .leaf rs' ss' (eqPairs p.sizes.length eqs) prods
  | .leafAt rs ss eqs prods => do
    let rs' ← rs.mapM fun (r,s) => do return (← boundRow bound p tab r,source p.sizes.length s)
    let ss' ← ss.mapM (proofStep bound p tab)
    return .leafAt rs' ss' (eqPairs p.sizes.length eqs) prods
  | .leafSq rs sqs ss eqs prods => do
    let rs' ← rs.mapM fun (r,s) => do return (← boundRow bound p tab r,source p.sizes.length s)
    let ss' ← ss.mapM (proofStep bound p tab)
    return .leafSq rs' (sqs.map (shiftRow p.sizes.length)) ss' (eqPairs p.sizes.length eqs) prods

def variableDefinition (bound : Nat) (p : Typing) : VDef → Option VDef
  | .var i => some (.var i)
  | .cell m k => some (.cell m (shiftRow p.sizes.length k))
  | .cellT m ks => some (.cellT m (ks.map (shiftRow p.sizes.length)))
  | .mono fs => some (.mono (fs.map (·+p.sizes.length)))
  | .term e => do return .term (← expr bound p e)

def certificate (bound : Nat) (p : Typing) (k : Kern.Cert) : Option Kern.Cert := do
  let tab ← k.1.mapM (variableDefinition bound p)
  let hyps ← k.2.1.mapM (condition bound p)
  let t ← tree bound p k.1 k.2.2
  return (p.sizes.map VDef.var ++ tab,hyps,t)

def law (bound : Nat) (p : Typing) (l : MLaw) : Option MLaw := do
  return {l with holds := ← condition bound p l.holds}

def scalarMachine (bound : Nat) (p : Typing) (m : MMachine) : Option MMachine := do
  return {m with
    init := ← m.init.mapM (fun (v,e) => do return (v,← expr bound p e))
    step := ← m.step.mapM (fun (v,e) => do return (v,← expr bound p e))
    writes := ← m.writes.mapM (fun (v,k,e) => do return (v,← expr bound p k,← expr bound p e))
    pre := ← condition bound p m.pre
    assume := ← condition bound p m.assume}

def pairInstances (bound : Nat) (p : Typing) (ps : List (Nat × E × List E)) : Option (List (Nat × E × List E)) :=
  ps.mapM fun (i,e,es) => do return (i,← expr bound p e,← es.mapM (expr bound p))

def machine (bound : Nat) (p : Typing) (s : SMachine) : Option SMachine := do
  let m ← scalarMachine bound p s.f.m
  let flags ← s.f.flags.mapM (fun (v,c) => do return (v,← condition bound p c))
  return {s with
    f := {s.f with m := m, flags := flags}
    every := ← s.every.mapM (fun (v,k,e) => do return (v,k,← expr bound p e))
    qflags := ← s.qflags.mapM (fun (v,ks,c) => do return (v,ks,← condition bound p c))
    facts := ← s.facts.mapM (law bound p)
    pfacts := ← s.pfacts.mapM (fun (l,ks) => do return (← law bound p l,ks))}

def entry (bound : Nat) (p : Typing) (e : SEntry) : Option SEntry := do
  return {e with
    law := ← law bound p e.law
    insts := ← e.insts.mapM (fun (i,x) => do return (i,← expr bound p x))
    qinsts := ← e.qinsts.mapM (fun (i,xs) => do return (i,← xs.mapM (expr bound p)))
    finsts := ← e.finsts.mapM (fun (i,x) => do return (i,← expr bound p x))
    pinsts := ← pairInstances bound p e.pinsts
    pfinsts := ← pairInstances bound p e.pfinsts
    start := ← certificate bound p e.start
    step := ← certificate bound p e.step}

/-- Drop only an optional named INIT-hypothesis cache. `checkIn` then checks the
same tree against the full goal reconstructed from the typed machine and law.
This does not delete a conjunct of that goal or add any size assumption. -/
def withoutInitialCache (e : SEntry) : SEntry :=
  {e with start := (e.start.1, [], e.start.2.2)}

def entryWithoutInitialCache (bound : Nat) (p : Typing) (e : SEntry) : Option SEntry :=
  entry bound p (withoutInitialCache e)

theorem initial_cache_tree_unchanged (e : SEntry) :
    (withoutInitialCache e).start.2.2 = e.start.2.2 := rfl

/-- Drop only the optional STEP-hypothesis cache. The ordinary checker must
validate the unchanged tree against the complete reconstructed STEP goal. -/
def withoutStepCache (e : SEntry) : SEntry :=
  {e with step := (e.step.1, [], e.step.2.2)}

theorem step_cache_tree_unchanged (e : SEntry) :
    (withoutStepCache e).step.2.2 = e.step.2.2 := rfl

def treeShape : Tree → List Nat
  | .split _ a b => 0 :: (treeShape a ++ treeShape b)
  | .leaf _ _ _ _ => [1]
  | .leafAt _ _ _ _ => [2]
  | .leafSq _ _ _ _ _ => [3]

/-- There is no trust in annotations or transport success: acceptance still
requires the complete original kernel checker on the translated machine. -/
theorem checked_transport (s : SMachine) (ps : List SEntry)
    (h : checkSMachine s ps = true) :
    ∀ ρ M, SReach s ρ M → ∀ e ∈ ps, e.Holds ρ M := smachine_sound _ _ h

#print axioms checked_transport
end Bapa.CertificateBoundSubstitution.Typed
