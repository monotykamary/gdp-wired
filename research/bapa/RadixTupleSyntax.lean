import RadixBinderExpansion

/-! Typed machine/law/instance syntax for packed-key certificate candidates.
Only map keys with declared layouts are re-keyed. A whole-address binder used
in an equality has to have an explicit RawAddress binding; unrelated arithmetic
is not rewritten. A map's `every` binder remains one raw tuple-encoded natural,
with projections used in its body. All resulting goals and tables must still be
accepted by the complete kernel. No source-bridge claim is made here. -/
namespace Bapa.RadixTupleSyntax
open Kern
open RadixKeySyntax

structure Config where
  radix : Nat := 64
  layouts : List (Nat × Nat)
  bindings : List RawAddress := []
  sizeVariable : Option Nat := none

/-- Bind a whole tuple address without adding free component parameters to a
machine. After a tuple key is substituted, these projections are linearizable. -/
def projectionParts : Nat → E → List E
  | 0, _ => []
  | 1, e => [e]
  | n+2, e => .proj 0 e :: projectionParts (n+1) (.proj 1 e)

def rawArity (cfg : Config) : E → Option Nat
  | .var v => (cfg.bindings.find? (fun b => b.variableId == v)).map (·.arity)
  | _ => none

def key (cfg : Config) (mp : Nat) (e : E) : Except Error E :=
  match RadixBinderExpansion.mapArity cfg.layouts mp with
  | none => .ok e
  | some arity => rekey cfg.radix arity cfg.bindings e

def equality (cfg : Config) (a b a' b' : E) : Except Error C := do
  match rawArity cfg a, rawArity cfg b with
  | none, none => do return .eq a' b'
  | some arity, none | none, some arity =>
    return .eq (← rekey cfg.radix arity cfg.bindings a')
      (← rekey cfg.radix arity cfg.bindings b')
  | some arity, some other =>
    if arity != other then throw (.unsupportedKey other)
    return .eq (← rekey cfg.radix arity cfg.bindings a')
      (← rekey cfg.radix arity cfg.bindings b')

mutual
  def expr (cfg : Config) : E → Except Error E
    | .var i => .ok (.var i)
    | .const n => .ok (.const n)
    | .add a b => do return .add (← expr cfg a) (← expr cfg b)
    | .sub a b => do return .sub (← expr cfg a) (← expr cfg b)
    | .mul n a => do return .mul n (← expr cfg a)
    | .min a b => do return .min (← expr cfg a) (← expr cfg b)
    | .max a b => do return .max (← expr cfg a) (← expr cfg b)
    | .prod a b => do return .prod (← expr cfg a) (← expr cfg b)
    | .ite p a b => do return .ite (← condition cfg p) (← expr cfg a) (← expr cfg b)
    | .get mp k => do return .get mp (← key cfg mp (← expr cfg k))
    | .tup a b => do return .tup (← expr cfg a) (← expr cfg b)
    | .proj i a => do return .proj i (← expr cfg a)
  def condition (cfg : Config) : C → Except Error C
    | .lt a (.const n) => do
      if n == cfg.radix then
        match cfg.sizeVariable with
        | none => do return trueC
        | some v => do return .lt (← expr cfg a) (.var v)
      return .lt (← expr cfg a) (.const n)
    | .le a (.const n) => do
      if n == cfg.radix then
        match cfg.sizeVariable with
        | none => do return trueC
        | some v => do return .le (← expr cfg a) (.var v)
      return .le (← expr cfg a) (.const n)
    | .lt a b => do return .lt (← expr cfg a) (← expr cfg b)
    | .le a b => do return .le (← expr cfg a) (← expr cfg b)
    | .eq a b => do equality cfg a b (← expr cfg a) (← expr cfg b)
    | .and a b => do return .and (← condition cfg a) (← condition cfg b)
    | .or a b => do return .or (← condition cfg a) (← condition cfg b)
    | .not a => do return .not (← condition cfg a)
end

def law (cfg : Config) (l : MLaw) : Except Error MLaw := do
  return {l with holds := ← condition cfg l.holds}

def scalarMachine (cfg : Config) (m : MMachine) : Except Error MMachine := do
  return {m with
    init := ← m.init.mapM (fun p => do return (p.1,← expr cfg p.2))
    step := ← m.step.mapM (fun p => do return (p.1,← expr cfg p.2))
    writes := ← m.writes.mapM (fun p => do
      let k ← key cfg p.1 (← expr cfg p.2.1)
      return (p.1,k,← expr cfg p.2.2))
    pre := ← condition cfg m.pre
    assume := ← condition cfg m.assume}

def machine (cfg : Config) (s : SMachine) : Except Error SMachine := do
  return {s with
    f := {s.f with
      m := ← scalarMachine cfg s.f.m
      flags := ← s.f.flags.mapM (fun p => do return (p.1,← condition cfg p.2))}
    every := ← s.every.mapM (fun p => do return (p.1,p.2.1,← expr cfg p.2.2))
    qflags := ← s.qflags.mapM (fun p => do return (p.1,p.2.1,← condition cfg p.2.2))
    facts := ← s.facts.mapM (law cfg)
    pfacts := ← s.pfacts.mapM (fun p => do return (← law cfg p.1,p.2))}

/-- Expand references to an expanded primary binder into the kernel's existing
multi-binder instance format. Profiles of laws and of facts are separate. -/
def instances (cfg : Config) (profiles : List (Nat × Nat))
    (single : List (Nat × E)) (multiple : List (Nat × E × List E)) :
    Except Error (List (Nat × E) × List (Nat × E × List E)) := do
  let (kept,expanded) ← RadixBinderExpansion.translateInstances cfg.radix profiles cfg.bindings single
  let original ← multiple.mapM (RadixBinderExpansion.translatePairInstance cfg.radix profiles cfg.bindings)
  let one ← kept.mapM (fun p => do return (p.1,← expr cfg p.2))
  let many ← (expanded ++ original).mapM (fun p => do
    return (p.1,← expr cfg p.2.1,← p.2.2.mapM (expr cfg)))
  return (one,many)

/-- This phase intentionally leaves certificate tables and trees untouched.
The complete translator must replace them before calling checkSMachine. -/
def entrySyntax (cfg : Config) (lawProfiles factProfiles : List (Nat × Nat))
    (e : SEntry) : Except Error SEntry := do
  let (insts,pinsts) ← instances cfg lawProfiles e.insts e.pinsts
  let (finsts,pfinsts) ← instances cfg factProfiles e.finsts e.pfinsts
  return {e with
    law := ← law cfg e.law
    insts := insts
    pinsts := pinsts
    finsts := finsts
    pfinsts := pfinsts
    qinsts := ← e.qinsts.mapM (fun p => do return (p.1,← p.2.mapM (expr cfg)))}

def expectedC (r : Except Error C) (c : C) : Bool :=
  match r with | .ok c' => beqC c' c | .error _ => false

def pairConfig : Config := ⟨64,[(0,2)],[],none⟩
def rawConfig : Config := ⟨64,[(0,2)],[⟨18,2,[.var 18,.var 100]⟩],none⟩

theorem pair_read : expected
    (expr pairConfig (.get 0 (.add (.mul 64 (.var 1)) (.var 2))))
    (.get 0 (.tup (.var 1) (.var 2))) = true := by decide +kernel

theorem raw_read : expected (expr rawConfig (.get 0 (.var 18)))
    (.get 0 (.tup (.var 18) (.var 100))) = true := by decide +kernel

theorem raw_comparison : expectedC
    (condition rawConfig (.eq (.var 18) (.add (.mul 64 (.var 1)) (.var 2))))
    (.eq (.tup (.var 18) (.var 100)) (.tup (.var 1) (.var 2))) = true := by decide +kernel

theorem unrelated_comparison : expectedC
    (condition pairConfig (.eq (.var 3) (.const 1)))
    (.eq (.var 3) (.const 1)) = true := by decide +kernel

theorem erased_bound : expectedC
    (condition pairConfig (.lt (.var 1) (.const 64))) trueC = true := by decide +kernel

theorem replaced_bound : expectedC
    (condition {pairConfig with sizeVariable := some 200} (.lt (.var 1) (.const 64)))
    (.lt (.var 1) (.var 200)) = true := by decide +kernel

theorem projection_arity : (projectionParts 3 (.var 40)).length = 3 := rfl

#print axioms pair_read
#print axioms raw_read
#print axioms raw_comparison
#print axioms unrelated_comparison
#print axioms erased_bound
#print axioms replaced_bound
#print axioms projection_arity
end Bapa.RadixTupleSyntax
