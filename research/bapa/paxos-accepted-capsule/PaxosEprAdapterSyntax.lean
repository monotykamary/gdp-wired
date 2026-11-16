import PaxosEprCountRekey
import PaxosEprPrefixTail
import RadixCertificateTransport

/-! Family-local candidate syntax. Recognized block comparisons lower to typed
coordinate comparisons; unknown packed orders are refused. Polynomial scalar
reconstruction is retained only for candidate certificate rows, never claimed
as the unbounded source order. Every candidate needs the full counted gate. -/
namespace Bapa.PaxosEprAdapterSyntax
open Kern RadixKeySyntax
abbrev Config := RadixTupleSyntax.Config

inductive Error where
  | key (reason : RadixKeySyntax.Error)
  | prefix (reason : PaxosEprPrefixTail.Error)
  | field (name : String) (reason : Error)
  | packedOrder
  | unsupportedCount (mp base : Nat)
  | table (column : Nat) (reason : String)
  deriving Repr

def atField {α : Type} (name : String) (r : Except Error α) : Except Error α :=
  r.mapError (Error.field name)

def pack (radix : Nat) : List E → E
  | [] => .const 0
  | [x] => x
  | x :: xs => .add (.mul (radix ^ xs.length) x) (pack radix xs)

/-- Prefix-tail fallback is typed; no unknown scalar is guessed to be a pair. -/
def parts (cfg : Config) (arity : Nat) (e : E) : Except Error (List E) :=
  match keyParts cfg.radix cfg.bindings arity e with
  | .ok ps => .ok ps
  | .error err =>
    if arity == 3 then
      (PaxosEprPrefixTail.prefixTailParts cfg.radix 1 2 cfg.bindings e).mapError Error.prefix
    else .error (.key err)

def key (cfg : Config) (mp : Nat) (e : E) : Except Error E :=
  match RadixBinderExpansion.mapArity cfg.layouts mp with
  | none => .ok e
  | some n => (parts cfg n e).map tuple

def scalar (cfg : Config) (v : Nat) : E :=
  match cfg.bindings.find? (fun b => b.variableId == v) with
  | none => .var v
  | some b => pack cfg.radix b.components

/-- Only a typed pair may participate in block-order lowering. -/
def pairParts (cfg : Config) (v : Nat) : Except Error (E × E) := do
  let ps ← parts cfg 2 (.var v)
  match ps with
  | [a,b] => return (a,b)
  | _ => throw (.key (.unsupportedKey 2))

/-- Values read from maps and explicit projections are scalars, not packed keys. -/
def rawScalar (cfg : Config) : E → Bool
  | .var v => cfg.bindings.any (fun b => b.variableId == v)
  | .add a b | .sub a b | .min a b | .max a b | .prod a b => rawScalar cfg a || rawScalar cfg b
  | .mul _ a => rawScalar cfg a
  | .tup _ _ => true
  | .ite _ a b => rawScalar cfg a || rawScalar cfg b
  | _ => false

def rejectOrder (cfg : Config) (a b : E) : Except Error Unit :=
  if rawScalar cfg a || rawScalar cfg b then .error .packedOrder else .ok ()

mutual
  def expr (cfg : Config) : E → Except Error E
    | .var v => .ok (scalar cfg v)
    | .const n => .ok (.const n)
    | .add a b => do return .add (← expr cfg a) (← expr cfg b)
    | .sub a b => do return .sub (← expr cfg a) (← expr cfg b)
    | .mul n a => do return .mul n (← expr cfg a)
    | .min a b => do return .min (← expr cfg a) (← expr cfg b)
    | .max a b => do return .max (← expr cfg a) (← expr cfg b)
    | .prod a b => do return .prod (← expr cfg a) (← expr cfg b)
    | .ite p a b => do return .ite (← condition cfg p) (← expr cfg a) (← expr cfg b)
    | .get mp k => do return .get mp (← key cfg mp k)
    -- Tuple components and projections already belong to the new representation.
    | .tup a b => .ok (.tup a b)
    | .proj i a => .ok (.proj i a)
  termination_by e => sizeOf e
  decreasing_by all_goals simp_all <;> omega
  def condition (cfg : Config) : C → Except Error C
    -- A same-block interval is typed membership, never a spilling numeric range.
    | .and (.le (.mul scale n) (.var v)) (.lt (.var w) (.add (.mul scale' n') r)) => do
      if scale == cfg.radix && scale' == cfg.radix && v == w && beqE n n' then
        let (a,b) ← pairParts cfg v
        return .and (.eq a (← expr cfg n)) (.lt b (← expr cfg r))
      throw .packedOrder
    | .lt (.var v) (.mul scale r) => do
      let translated ← expr cfg r
      if scale == cfg.radix && RadixTupleSyntax.rawArity cfg (.var v) == some 2 then
        let (a,_) ← pairParts cfg v
        match translated with
        | .add x (.const 1) => return .le a x
        | _ => return .lt a translated
      rejectOrder cfg (.var v) (.mul scale r)
      return .lt (scalar cfg v) (.mul scale translated)
    | .lt a (.const n) => do
      rejectOrder cfg a (.const n)
      if n == cfg.radix then return trueC
      return .lt (← expr cfg a) (.const n)
    | .le a (.const n) => do
      rejectOrder cfg a (.const n)
      if n == cfg.radix || n + 1 == cfg.radix then return trueC
      return .le (← expr cfg a) (.const n)
    | .lt a b => do rejectOrder cfg a b; return .lt (← expr cfg a) (← expr cfg b)
    | .le a b => do rejectOrder cfg a b; return .le (← expr cfg a) (← expr cfg b)
    | .eq a b => do
      match RadixTupleSyntax.rawArity cfg a, RadixTupleSyntax.rawArity cfg b with
      | none, none => return .eq (← expr cfg a) (← expr cfg b)
      | some n, none | none, some n => return .eq (tuple (← parts cfg n a)) (tuple (← parts cfg n b))
      | some n, some m =>
        if n != m then throw (.key (.unsupportedKey m))
        return .eq (tuple (← parts cfg n a)) (tuple (← parts cfg n b))
    | .and a b => do return .and (← condition cfg a) (← condition cfg b)
    | .or a b => do return .or (← condition cfg a) (← condition cfg b)
    | .not a => do return .not (← condition cfg a)
  termination_by c => sizeOf c
  decreasing_by all_goals simp_all <;> omega
end

def law (cfg : Config) (l : MLaw) : Except Error MLaw := do
  return {l with holds := ← condition cfg l.holds}

def machine (cfg : Config) (s : SMachine) : Except Error SMachine := do
  return {s with
    f := {s.f with
      m := {s.f.m with
        init := ← s.f.m.init.mapM (fun p => do return (p.1,← atField s!"init[{p.1}]" (expr cfg p.2)))
        step := ← s.f.m.step.mapM (fun p => do return (p.1,← atField s!"step[{p.1}]" (expr cfg p.2)))
        writes := ← s.f.m.writes.mapM (fun p => do
          return (p.1,← atField s!"writes[{p.1}].key" (key cfg p.1 p.2.1),
            ← atField s!"writes[{p.1}].value" (expr cfg p.2.2)))
        pre := ← atField "pre" (condition cfg s.f.m.pre)
        assume := ← atField "assume" (condition cfg s.f.m.assume)}
      flags := ← s.f.flags.mapM (fun p => do return (p.1,← atField s!"flags[{p.1}]" (condition cfg p.2)))}
    every := ← s.every.mapM (fun p => do return (p.1,p.2.1,← atField s!"every[{p.1}]" (expr cfg p.2.2)))
    qflags := ← s.qflags.mapM (fun p => do
      if p.1 == 72 && p.2.1 != [133] then throw (.key (.unsupportedKey 2))
      return (p.1,if p.1 == 72 then [133,2000000] else p.2.1,
        ← atField s!"qflags[{p.1}]" (condition cfg p.2.2)))
    wits := ← s.wits.mapM (fun p => do
      if p.1 == 72 && p.2 != [84] then throw (.key (.unsupportedKey 2))
      return (p.1,if p.1 == 72 then [84,2000001] else p.2))
    facts := ← s.facts.mapM (law cfg)
    pfacts := ← s.pfacts.mapM (fun p => do return (← law cfg p.1,p.2))}

-- Retained scan-prefix law 12 binds a scalar node first and a pair tail second.
def extraArguments (cfg : Config) (lawId : Nat) (args : List E) : Except Error (List E) :=
  (args.zipIdx.mapM fun (e,i) =>
    if lawId == 12 && i == 0 then parts cfg 2 e else do return [← expr cfg e]).map List.flatten

def pairInstance (cfg : Config) (profiles : List (Nat × Nat)) (p : Nat × E × List E) :
    Except Error (Nat × E × List E) := do
  match profiles.find? (fun q => q.1 == p.1) with
  | none => return (p.1,← expr cfg p.2.1,← extraArguments cfg p.1 p.2.2)
  | some profile =>
    let ps ← parts cfg profile.2 p.2.1
    match ps with
    | [] => throw (.key (.unsupportedKey profile.2))
    | a :: rest => return (p.1,a,rest ++ (← extraArguments cfg p.1 p.2.2))

def instances (cfg : Config) (profiles : List (Nat × Nat))
    (single : List (Nat × E)) (multiple : List (Nat × E × List E)) :
    Except Error (List (Nat × E) × List (Nat × E × List E)) := do
  let mut kept := []
  let mut expanded := []
  for p in single do
    if profiles.any (fun q => q.1 == p.1) then
      expanded := expanded ++ [← pairInstance cfg profiles (p.1,p.2,[])]
    else kept := kept ++ [(p.1,← expr cfg p.2)]
  return (kept,expanded ++ (← multiple.mapM (pairInstance cfg profiles)))

def entry (cfg : Config) (profiles : List (Nat × Nat)) (e : SEntry) : Except Error SEntry := do
  let (insts,pinsts) ← atField "law-instances" (instances cfg profiles e.insts e.pinsts)
  let (finsts,pfinsts) ← atField "fact-instances" (instances cfg [] e.finsts e.pfinsts)
  let translatedLaw ← atField "law" (law cfg e.law)
  let qinsts ← e.qinsts.mapM (fun p => do
    if p.1 == 72 then
      match p.2 with
      | [k] => return (p.1,← atField "qinsts[72]" (parts cfg 2 k))
      | _ => throw (.key (.unsupportedKey 2))
    return (p.1,← p.2.mapM (expr cfg)))
  return {e with
    law := translatedLaw
    insts := insts
    pinsts := pinsts
    finsts := finsts
    pfinsts := pfinsts
    qinsts := qinsts
    keys2 := if e.law.key == some 28 && e.keys2 == [29] then [29,2000002] else e.keys2}

/-- Invoke the proven unary reparameterization BEFORE physical map re-keying. -/
def declaration (cfg : Config) (d : CDecl) : Except Error CDecl := do
  if d.base != 0 && d.base != cfg.radix then throw (.unsupportedCount d.mp d.base)
  let u := if d.base == 0 then d else PaxosEprCountRekey.unary d
  return {u with
    below := ← atField "below" (expr cfg u.below)
    body := ← atField "body" (expr cfg u.body)}

def exampleConfig : Config := ⟨64,[(4,3),(11,2),(16,2)],
  [⟨133,2,[.proj 0 (.var 133),.proj 1 (.var 133)]⟩],some 1⟩

theorem prefix_count_key : RadixKeySyntax.expected
    ((key exampleConfig 4 (.add (.mul 4096 (.var 9)) (.var 133))).mapError (fun _ => .unsupportedKey 3))
    (.tup (.var 9) (.tup (.proj 0 (.var 133)) (.proj 1 (.var 133)))) = true := by decide +kernel

theorem pair_count_key : RadixKeySyntax.expected
    ((key exampleConfig 16 (.add (.mul 64 (.var 4)) (.var 5))).mapError (fun _ => .unsupportedKey 2))
    (.tup (.var 4) (.var 5)) = true := by decide +kernel

/-- Numeric row-candidate meaning only; not the typed target comparison policy. -/
theorem packed_order (ρ : Nat → Nat) (M : Nat → Nat → Nat) (a b r : Nat) :
    evalC (upd ρ 133 (cpair a b)) M
      (.lt (scalar exampleConfig 133) (.mul 64 (.const r))) =
      decide (64*a+b < 64*r) := by
  simp [scalar, exampleConfig, pack, evalC, evalE, upd, pickP]

theorem size_not_64 :
    (declaration exampleConfig ⟨11,16,95,97,.var 1,.const 1,96,64⟩).toOption.map
      (fun d => (d.base,beqE d.below (.var 1))) = some (0,true) := by decide +kernel

/-- Exactly the old finite-coordinate justification, not an unbounded rewrite. -/
theorem before_block (a b r : Nat) (hb : b < 64) :
    (64*a+b < 64*r) ↔ a < r := by omega

theorem block_interval (a b n r : Nat) (hb : b < 64) (hr : r ≤ 64) :
    (64*n ≤ 64*a+b ∧ 64*a+b < 64*n+r) ↔ (a=n ∧ b<r) := by omega

theorem arbitrary_rounds_and_values :
    (condition exampleConfig (.lt (.var 4) (.const 64))).toOption = some trueC ∧
    (condition exampleConfig (.le (.var 5) (.const 63))).toOption = some trueC := by decide +kernel

theorem typed_before_block :
    (condition exampleConfig (.lt (.var 133) (.mul 64 (.var 10)))).toOption =
      some (.lt (.proj 0 (.var 133)) (.var 10)) := by decide +kernel

theorem typed_upper_block :
    (condition exampleConfig (.lt (.var 133) (.mul 64 (.add (.var 11) (.const 1))))).toOption =
      some (.le (.proj 0 (.var 133)) (.var 11)) := by decide +kernel

-- Concrete refusals of any unconditional polynomial/typed equivalence.
theorem unbounded_interval_spill :
    (64*0 ≤ 64*1+0 ∧ 64*1+0 < 64*0+65) ∧ ¬(1=0 ∧ 0<65) := by decide +kernel

theorem unbounded_before_block_spill :
    ¬(64*0+64 < 64*1) ∧ 0<1 := by decide +kernel

theorem typed_interval :
    (condition exampleConfig (.and (.le (.mul 64 (.var 3)) (.var 133))
      (.lt (.var 133) (.add (.mul 64 (.var 3)) (.var 4))))).toOption =
      some (.and (.eq (.proj 0 (.var 133)) (.var 3)) (.lt (.proj 1 (.var 133)) (.var 4))) := by decide +kernel

theorem unsupported_order_refused :
    (condition exampleConfig (.lt (.var 133) (.var 10))).toOption = none := by decide +kernel

#print axioms prefix_count_key
#print axioms before_block
#print axioms block_interval
#print axioms unbounded_interval_spill
#print axioms unbounded_before_block_spill
#print axioms typed_before_block
#print axioms arbitrary_rounds_and_values
#print axioms typed_upper_block
#print axioms typed_interval
#print axioms unsupported_order_refused
#print axioms pair_count_key
#print axioms packed_order
#print axioms size_not_64
end Bapa.PaxosEprAdapterSyntax
