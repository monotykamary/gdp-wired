import RadixKeySyntax

/-! The table/column phase of retained certificate re-keying. Every old column
keeps its relative position, after an explicit shift of fresh component
variables. Thus rows, monomials, cell-equality pairs and source hints have one
uniform column map. A typed packed cell becomes a tuple cell. This constructs
candidate syntax only: it is NOT a validity-preservation claim. The complete
kernel must recheck it, and a source-to-target bridge remains a separate duty. -/
namespace Bapa.RadixCertificateTable
open Kern
open RadixKeySyntax

inductive Error where
  | key (reason : RadixKeySyntax.Error)
  | nonNaturalKeyRow
  | missingComponentColumn (variableId : Nat)
  | malformedTupleCell (map expected actual : Nat)
  deriving Repr, BEq

/-- New variables go before every old definition, never after a dependent cell. -/
def freshVariables (tab : List VDef) (bindings : List RawAddress) : List Nat :=
  (bindings.flatMap (fun b => b.components.filterMap fun e =>
    match e with | .var v => some v | _ => none)).foldl (fun acc v =>
      if (findIdx (isVar v) tab).isSome || acc.contains v then acc else acc ++ [v]) []

def row (shift : Nat) (r : Cert.Row) : Cert.Row :=
  ⟨r.coefs.map (fun (i,c) => (i+shift,c)),r.const⟩

def pairs (shift : Nat) (ps : List (Nat × Nat)) : List (Nat × Nat) :=
  ps.map (fun (i,j) => (i+shift,j+shift))

def source (shift : Nat) : Src → Src
  | .nat i => .nat (i+shift)
  | .term i => .term (i+shift)
  | s => s

/-- Arithmetic-step references name rows, not columns. Only an explicit cut
row contains columns; its source-row index and multiplier stay unchanged. -/
def proofStep (shift : Nat) : Cert.Step → Cert.Step
  | .cut i g q c => let r := row shift ⟨q,c⟩; .cut i g r.coefs r.const
  | s => s

/-- A completely mechanical column relocation, with no pruning or leaf repair. -/
def relocateTree (shift : Nat) : Tree → Tree
  | .split r a b => .split (row shift r) (relocateTree shift a) (relocateTree shift b)
  | .leaf rs ss eqs prods =>
    .leaf (rs.map (row shift)) (ss.map (proofStep shift)) (pairs shift eqs) prods
  | .leafAt rs ss eqs prods =>
    .leafAt (rs.map (fun (r,s) => (row shift r,source shift s)))
      (ss.map (proofStep shift)) (pairs shift eqs) prods
  | .leafSq rs sqs ss eqs prods =>
    .leafSq (rs.map (fun (r,s) => (row shift r,source shift s)))
      (sqs.map (row shift)) (ss.map (proofStep shift)) (pairs shift eqs) prods

/-- Formal polynomial place of one positive coefficient, capped at arity-1.
This is not an injectivity assertion about the old finite-radix encoding. -/
def coefficientPlace (radix : Nat) : Nat → Nat → Nat × Nat
  | 0, n => (0,n)
  | fuel+1, n =>
    if radix > 1 && n > 0 && n % radix == 0 then
      let (p,k) := coefficientPlace radix fuel (n / radix)
      (p+1,k)
    else (0,n)

def componentRow (radix arity component shift : Nat) (r : Cert.Row) : Cert.Row :=
  let cs := r.coefs.filterMap fun (j,c) =>
    let (place,k) := coefficientPlace radix (arity-1) c.natAbs
    if place + component + 1 == arity then some (j+shift,(k : Int)) else none
  let constant := ((literalParts radix arity r.const.natAbs)[component]?.getD (.const 0))
  let n := match constant with | .const n => n | _ => 0
  ⟨cs,n⟩

def components (radix arity : Nat) (bindings : List RawAddress)
    (oldTab newVars : List VDef) (r : Cert.Row) : Except Error (List Cert.Row) := do
  let shift := newVars.length
  if radix < 2 || arity < 2 then throw (.key (.unsupportedKey arity))
  -- A raw address must have an explicitly typed binder expansion. Never treat
  -- an unknown scalar variable as an already-decoded final component.
  match r.coefs with
  | [(j,1)] =>
    if r.const == 0 then
      match oldTab[j]? with
      | some (.var v) =>
        let b ← match bindings.find? (fun b => b.variableId == v && b.arity == arity) with
          | some b => pure b
          | none => throw (.key (.needBinderExpansion v arity))
        if b.components.length != arity then
          throw (.key (.malformedBinder v arity b.components.length))
        let basis := newVars ++ oldTab
        b.components.mapM fun e =>
          match linear basis [] e with
          | some r => pure r
          | none => throw (.missingComponentColumn v)
      | _ => throw (.key (.unsupportedKey arity))
    else decompose shift
  | _ => decompose shift
where
  decompose shift :=
    if r.const < 0 || r.coefs.any (fun p => p.2 < 0) then .error .nonNaturalKeyRow
    else .ok ((List.range arity).map (fun i => componentRow radix arity i shift r))

/-- The caller supplies the same typed expression translator used for the
machine and law. Unknown maps remain unary; an already-tuple cell must have its
stated arity. Any later mismatch with a goal is rejected by the kernel. -/
def table (radix : Nat) (layouts : List (Nat × Nat)) (bindings : List RawAddress)
    (translate : E → Except Error E) (tab : List VDef) : Except Error (List VDef) := do
  let vars := (freshVariables tab bindings).map VDef.var
  let shift := vars.length
  let old ← tab.mapM fun d => do
    match d with
    | .var v => pure (.var v)
    | .mono js => pure (.mono (js.map (·+shift)))
    | .term e => return .term (← translate e)
    | .cell m key =>
      match (layouts.find? (fun p => p.1 == m)).map (·.2) with
      | none => pure (.cell m (row shift key))
      | some arity => return .cellT m (← components radix arity bindings tab vars key)
    | .cellT m keys =>
      match (layouts.find? (fun p => p.1 == m)).map (·.2) with
      | some arity =>
        if keys.length != arity then throw (.malformedTupleCell m arity keys.length)
        else pure (.cellT m (keys.map (row shift)))
      | none => pure (.cellT m (keys.map (row shift)))
  return vars ++ old

/-- Relocation does not conflate distinct cell columns. -/
theorem column_map_injective (shift i j : Nat) : i+shift = j+shift ↔ i=j := by omega

theorem moved_bound_row :
    (row 3 (sp [(2,1)] (-63))).coefs = [(5,1)] ∧
    (row 3 (sp [(2,1)] (-63))).const = -63 := by decide +kernel

def expectedComponents (result : Except Error (List Cert.Row))
    (expected : List (List (Nat × Int) × Int)) : Bool :=
  match result with
  | .ok rs => rs.map (fun r => (r.coefs,r.const)) == expected
  | .error _ => false

theorem packed_pair_components : expectedComponents
    (components 64 2 [] [.var 0,.var 1] [] (sp [(0,64),(1,1)] 0))
    [([(0,1)],0), ([(1,1)],0)] = true := by decide +kernel

theorem packed_triple_components : expectedComponents
    (components 64 3 [] [.var 0,.var 1,.var 2] [] (sp [(0,4096),(1,64),(2,1)] 0))
    [([(0,1)],0), ([(1,1)],0), ([(2,1)],0)] = true := by decide +kernel

def rawAddressRefused : Bool :=
  match components 64 2 [] [.var 18] [] (sp [(0,1)] 0) with
  | .error (.key (.needBinderExpansion 18 2)) => true
  | _ => false

theorem unknown_raw_address_refused : rawAddressRefused = true := by decide +kernel

theorem raw_address_components : expectedComponents
    (components 64 2 [⟨18,2,[.var 18,.var 100]⟩] [.var 18] [.var 100]
      (sp [(0,1)] 0)) [([(1,1)],0), ([(0,1)],0)] = true := by decide +kernel

#print axioms column_map_injective
#print axioms moved_bound_row
#print axioms packed_pair_components
#print axioms packed_triple_components
#print axioms unknown_raw_address_refused
#print axioms raw_address_components
end Bapa.RadixCertificateTable
