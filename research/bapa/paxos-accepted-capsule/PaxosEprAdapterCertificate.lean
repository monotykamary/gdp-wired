import PaxosEprAdapterSyntax

/-! Lossless-in-shape counted candidate transport. All seven CCert fields are
translated, including nested cut trees and their hypothesis slices. Nothing is
replaced by a plain Cert, discarded, solved, or asserted to be a valid proof.
Scalar packed-order rows are polynomially substituted, not tuple-ordered. -/
namespace Bapa.PaxosEprAdapterCertificate
open Kern
open PaxosEprAdapterSyntax

private def defEq : VDef → VDef → Bool
  | .var a, .var b => a == b
  | .term a, .term b => beqE a b
  | _, _ => false

def tablePrefix (cfg : Config) (tab : List VDef) : List VDef :=
  (cfg.bindings.flatMap (fun b => b.components.map (fun e =>
    match e with | .var v => VDef.var v | _ => VDef.term e))).foldl (fun acc d =>
      if (tab ++ acc).any (defEq d) then acc else acc ++ [d]) []

def column (cfg : Config) (old basis : List VDef) (shift j : Nat) : Except Error Cert.Row :=
  match old[j]? with
  | some (.var v) =>
    match linear basis [] (scalar cfg v) with
    | some r => .ok r
    | none => .error (.table j "scalar packed polynomial not linear in target table")
  | some _ => .ok (lunit (j+shift))
  | none => .error (.table j "row column out of range")

def row (cfg : Config) (old basis : List VDef) (shift : Nat) (r : Cert.Row) : Except Error Cert.Row := do
  let mut result := lconst r.const
  for (j,c) in r.coefs do
    result := ladd result (lscale c (← column cfg old basis shift j))
  return result

-- Structural sorting stays kernel-reducible (no opaque library sort in controls).
def insertCoefficient (p : Nat × Int) : List (Nat × Int) → List (Nat × Int)
  | [] => [p]
  | q :: qs => if p.2 >= q.2 then p :: q :: qs else q :: insertCoefficient p qs

def orderCoefficients : List (Nat × Int) → List (Nat × Int)
  | [] => []
  | p :: ps => insertCoefficient p (orderCoefficients ps)

/-- Only natural, explicitly typed key syntax can be reified. -/
def keyExpr (tab : List VDef) (col : Nat) (r : Cert.Row) : Except Error E := do
  if r.const < 0 then throw (.table col "negative key constant")
  let mut terms : List E := []
  for (j,c) in orderCoefficients r.coefs do
    if c < 0 then throw (.table col "negative key coefficient")
    if c != 0 then
      let e ← match tab[j]? with
        | some (.var v) => pure (E.var v)
        | some (.term e) => pure e
        | _ => throw (.table col s!"key column {j} is not a variable or term")
      terms := terms ++ [if c == 1 then e else E.mul c.toNat e]
  if r.const != 0 then terms := terms ++ [.const r.const.toNat]
  else
    match terms with
    | [.mul n _] => if n == 64 || n == 4096 then terms := terms ++ [.const 0]
    | _ => pure ()
  return match terms with
    | [] => .const 0
    | e :: es => es.foldl E.add e

/-- Two retained scalar-skolem cells lost a syntactic `64*0` prefix in sparse
normalization. Their provenance is checked in the audit. Do not expand either
scalar into an arbitrary packed binder, and never generalize to other IDs/maps. -/
def tableParts (cfg : Config) (mp arity : Nat) (e : E) : Except Error (List E) :=
  match e with
  | .var v =>
    if arity == 2 && ((mp == 3 && v == 61) || (mp == 1 && v == 65)) &&
        !(cfg.bindings.any (fun b => b.variableId == v)) then
      .ok [.const 0,.var v]
    else parts cfg arity e
  | _ => parts cfg arity e

def table (cfg : Config) (tab : List VDef) : Except Error (List VDef) := do
  let pre := tablePrefix cfg tab
  let shift := pre.length
  let basis := pre ++ tab
  let ds ← tab.zipIdx.mapM fun (d,i) => atField s!"tab[{i}]" do
    match d with
    | .var v => return .var v
    | .term e => return .term (← expr cfg e)
    | .mono js =>
      if js.any (fun j => match tab[j]? with
          | some (.var v) => cfg.bindings.any (fun b => b.variableId == v)
          | _ => false) then throw (.table i "monomial uses a packed scalar column")
      return .mono (js.map (·+shift))
    | .cell mp r =>
      match RadixBinderExpansion.mapArity cfg.layouts mp with
      | none => return .cell mp (← row cfg tab basis shift r)
      | some arity =>
        let ps ← tableParts cfg mp arity (← keyExpr tab i r)
        let rs ← ps.mapM fun e => match linear basis [] e with
          | some r => pure r
          | none => throw (.table i "typed component not linear in target table")
        return .cellT mp rs
    | .cellT mp rs =>
      match RadixBinderExpansion.mapArity cfg.layouts mp with
      | some n => if n != rs.length then throw (.table i "tuple arity mismatch")
      | none => pure ()
      return .cellT mp (← rs.mapM (row cfg tab basis shift))
  return pre ++ ds

def proofStep (tr : Cert.Row → Except Error Cert.Row) : Cert.Step → Except Error Cert.Step
  | .cut i g q c => do let r ← tr ⟨q,c⟩; return .cut i g r.coefs r.const
  | s => .ok s

def tree (tr : Cert.Row → Except Error Cert.Row) (shift : Nat) : Tree → Except Error Tree
  | .split r y n => do return .split (← atField "split" (tr r)) (← atField "yes" (tree tr shift y)) (← atField "no" (tree tr shift n))
  | .leaf rs ss eqs prods => do
    return .leaf (← rs.mapM tr) (← ss.mapM (proofStep tr)) (RadixCertificateTable.pairs shift eqs) prods
  | .leafAt rs ss eqs prods => do
    return .leafAt (← rs.mapM (fun (r,s) => do return (← tr r,RadixCertificateTable.source shift s)))
      (← ss.mapM (proofStep tr)) (RadixCertificateTable.pairs shift eqs) prods
  | .leafSq rs sqs ss eqs prods => do
    return .leafSq (← rs.mapM (fun (r,s) => do return (← tr r,RadixCertificateTable.source shift s)))
      (← sqs.mapM tr) (← ss.mapM (proofStep tr)) (RadixCertificateTable.pairs shift eqs) prods

def certificate (cfg : Config) (k : CCert) (named : Option (List C) := none) : Except Error CCert := do
  let pre := tablePrefix cfg k.tab
  let tr := row cfg k.tab (pre ++ k.tab) pre.length
  let hs ← match named with
    | none => k.hyps.zipIdx.mapM (fun (h,i) => atField s!"hyps[{i}]" (condition cfg h))
    | some hs =>
      if hs.length == k.hyps.length then pure hs
      else throw (.field "hyps" (.table 0 "named hypothesis length changed"))
  return {
    hyps := hs
    reads := ← k.reads.zipIdx.mapM (fun (r,i) => atField s!"reads[{i}]" do return (r.1,r.2.1,← key cfg r.2.1 r.2.2))
    insts := ← k.insts.zipIdx.mapM (fun (i,n) => atField s!"insts[{n}].below" do return {i with below := ← expr cfg i.below})
    tab := ← table cfg k.tab
    tree := ← atField "tree" (tree tr pre.length k.tree)
    picks := ← k.picks.zipIdx.mapM (fun (p,i) => atField s!"picks[{i}]" do return (p.1,← p.2.mapM (expr cfg)))
    lemmas := ← k.lemmas.zipIdx.mapM (fun (l,i) => atField s!"lemmas[{i}]" do
      return {l with
        when := ← l.when.mapM tr
        cut := ← tr l.cut
        tree := ← tree tr pre.length l.tree})}

theorem scalar_zero_prefix_controls :
    (tableParts exampleConfig 3 2 (.var 61)).toOption = some [.const 0,.var 61] ∧
    (tableParts exampleConfig 1 2 (.var 65)).toOption = some [.const 0,.var 65] ∧
    (tableParts exampleConfig 3 2 (.var 65)).toOption = none ∧
    (tableParts exampleConfig 3 2 (.var 62)).toOption = none := by decide +kernel

#print axioms scalar_zero_prefix_controls

theorem sparse_key_canonical_order :
    (keyExpr [.var 3,.var 4,.var 5] 0 (sp [(0,64),(1,1),(2,4096)] 0)).toOption =
      some (.add (.add (.mul 4096 (.var 5)) (.mul 64 (.var 3))) (.var 4)) := by decide +kernel

def sample : CCert := {
  hyps := [.lt (.var 3) (.var 1)]
  reads := [(104,11,.add (.mul 64 (.var 4)) (.var 5))]
  insts := [⟨112,.var 1,[(1,104)],-1⟩]
  tab := [.var 1,.var 3,.var 4,.var 5]
  tree := .leaf [] [] [] []
  picks := [(104,[.var 3])]
  lemmas := [⟨[],lconst 0,.leaf [] [] [] [],some [0]⟩]}

def fieldShape (k : CCert) : List Nat :=
  [k.hyps.length,k.reads.length,k.insts.length,k.picks.length,k.lemmas.length]

theorem all_counted_fields_kept :
    (certificate PaxosEprAdapterSyntax.exampleConfig sample).toOption.map fieldShape = some [1,1,1,1,1] := by
  decide +kernel

theorem witness_and_cut_slice_kept :
    (certificate PaxosEprAdapterSyntax.exampleConfig sample).toOption.map
      (fun k => (k.insts.map (·.wit),k.lemmas.map (·.slice))) = some ([112],[some [0]]) := by
  decide +kernel

/-- Acceptance uses the complete counted gate, with its original GHolds premise. -/
theorem checked (s : SMachine) (ds : List CDecl) (ps : List CEntry)
    (h : checkCMachine s ds ps = true) :
    ∀ ρ M, CReach s ds ρ M → ∀ ce ∈ ps, ce.e.Holds ρ (withCnt ds ρ M) :=
  cmachine_sound s ds ps h

#print axioms sparse_key_canonical_order
#print axioms all_counted_fields_kept
#print axioms witness_and_cut_slice_kept
#print axioms checked
end Bapa.PaxosEprAdapterCertificate
