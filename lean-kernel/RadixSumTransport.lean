import RadixCertificateTransport
import Sums

/-! Shape-parameterized radix candidate generation with opaque SUM addresses.
No source names, fixed basis, fixed radix, law indices or SUM identifiers occur.
This module constructs data only. Complete family and source checking are
separate mandatory obligations; a failed conversion never returns an old family.
-/
namespace Bapa.RadixSumTransport
open Kern
open RadixKeySyntax

structure Plan where
  radix : Nat
  layouts : List (Nat × Nat)
  freshBase : Nat
  /-- Quantified SUM flags whose single argument denotes an opaque address. -/
  sumFlags : List (Nat × Nat)

abbrev Error := RadixCertificateTransport.Error

def layout (p : Plan) (mp : Nat) : Option Nat :=
  RadixBinderExpansion.mapArity p.layouts mp

def config (p : Plan) (bs : List RawAddress := []) : RadixTupleSyntax.Config :=
  ⟨p.radix,p.layouts,bs,none⟩

/-- Unbound scalar addresses are already raw SUM addresses, not components. -/
def address (p : Plan) (arity : Nat) (bs : List RawAddress) (e : E) : Except RadixKeySyntax.Error E :=
  match e with
  | .var v => if bs.any (fun b => b.variableId == v) then rekey p.radix arity bs e else .ok e
  | _ => rekey p.radix arity bs e

mutual
  def expr (p : Plan) (bs : List RawAddress) : E → Except RadixKeySyntax.Error E
    | .var v => .ok (.var v)
    | .const n => .ok (.const n)
    | .get m k => do
      let k' ← match layout p m with
        | some arity => address p arity bs k
        | none => expr p bs k
      return .get m k'
    | .add a b => do return .add (← expr p bs a) (← expr p bs b)
    | .sub a b => do return .sub (← expr p bs a) (← expr p bs b)
    | .mul n a => do return .mul n (← expr p bs a)
    | .min a b => do return .min (← expr p bs a) (← expr p bs b)
    | .max a b => do return .max (← expr p bs a) (← expr p bs b)
    | .prod a b => do return .prod (← expr p bs a) (← expr p bs b)
    | .ite c a b => do return .ite (← cond p bs c) (← expr p bs a) (← expr p bs b)
    | .tup a b => do return .tup (← expr p bs a) (← expr p bs b)
    | .proj n a => do return .proj n (← expr p bs a)
  def cond (p : Plan) (bs : List RawAddress) : C → Except RadixKeySyntax.Error C
    | .lt a b => do return .lt (← expr p bs a) (← expr p bs b)
    | .le a b => do return .le (← expr p bs a) (← expr p bs b)
    | .eq a b => do
      let ca := RadixTupleSyntax.rawArity (config p bs) a
      let cb := RadixTupleSyntax.rawArity (config p bs) b
      match ca, cb with
      | none, none => return .eq (← expr p bs a) (← expr p bs b)
      | some n, none | none, some n => return .eq (← address p n bs a) (← address p n bs b)
      | some n, some m =>
        if n != m then throw (.unsupportedKey m)
        return .eq (← address p n bs a) (← address p n bs b)
    | .and a b => do return .and (← cond p bs a) (← cond p bs b)
    | .or a b => do return .or (← cond p bs a) (← cond p bs b)
    | .not a => do return .not (← cond p bs a)
end

def isOpaque (bs : List RawAddress) (tab : List VDef) (r : Cert.Row) : Bool :=
  match r.coefs with
  | [(j,1)] => r.const == 0 && (match tab[j]? with
      | some (.var v) => !(bs.any (fun b => b.variableId == v))
      | _ => false)
  | _ => false

def table (p : Plan) (bs : List RawAddress) (old : List VDef) : Except RadixCertificateTable.Error (List VDef) := do
  let fresh := (RadixCertificateTable.freshVariables old bs).map VDef.var
  let shift := fresh.length
  let moved ← old.mapM fun d => do
    match d with
    | .var v => pure (.var v)
    | .mono js => pure (.mono (js.map (·+shift)))
    | .term e => match expr p bs (CertificateBoundErasure.expr p.radix e) with
      | .ok e' => pure (.term e')
      | .error error => throw (.key error)
    | .cell m k => match layout p m with
      | none => pure (.cell m (RadixCertificateTable.row shift k))
      | some n => if isOpaque bs old k then pure (.cell m (RadixCertificateTable.row shift k)) else
          return .cellT m (← RadixCertificateTable.components p.radix n bs old fresh k)
    | .cellT m ks => pure (.cellT m (ks.map (RadixCertificateTable.row shift)))
  return fresh ++ moved

def certificate (p : Plan) (bs : List RawAddress) (goal : List C) (k : Kern.Cert) : Except Error Kern.Cert := do
  let tab ← RadixCertificateTransport.liftTable (table p bs k.1)
  let shift := tab.length-k.1.length
  let plans := RadixEqualityTree.plans shift k.1 tab
  return CertificateBooleanCleanup.certificate goal
    (tab,[],RadixEqualityTree.tree shift (some p.radix) plans [] k.2.2)

def instanceParts (p : Plan) (n : Nat) (bs : List RawAddress) (e : E) : Except RadixKeySyntax.Error (List E) :=
  match e with
  | .var v => if bs.any (fun b => b.variableId == v) then keyParts p.radix bs n e
      else .ok (RadixTupleSyntax.projectionParts n e)
  | _ => keyParts p.radix bs n e

def entry (p : Plan) (profiles : List (Nat × Nat)) (bs : List RawAddress) (e : SEntry) : Except RadixKeySyntax.Error SEntry := do
  let mut one := []
  let mut many := []
  for (i,k) in e.insts do
    match RadixBinderExpansion.mapArity profiles i with
    | some n => match ← instanceParts p n bs k with
      | a :: rest => many := many ++ [(i,a,rest)]
      | [] => throw (.unsupportedKey n)
    | none => one := one ++ [(i,← expr p bs k)]
  for (i,k,ks) in e.pinsts do
    match RadixBinderExpansion.mapArity profiles i with
    | some n => match ← instanceParts p n bs k with
      | a :: rest => many := many ++ [(i,a,rest ++ (← ks.mapM (expr p bs)))]
      | [] => throw (.unsupportedKey n)
    | none => many := many ++ [(i,← expr p bs k,← ks.mapM (expr p bs))]
  return {e with
    law := {e.law with holds := ← cond p bs (CertificateBoundErasure.condition p.radix e.law.holds)}
    insts := one, pinsts := many
    qinsts := ← e.qinsts.mapM (fun (i,ks) => do
      match RadixBinderExpansion.mapArity p.sumFlags i with
      | none => return (i,← ks.mapM (expr p bs))
      | some n => match ks with
        | [k] => return (i,[← address p n bs k])
        | _ => throw (.unsupportedKey n))
    finsts := ← e.finsts.mapM (fun (i,k) => do return (i,← expr p bs k))
    pfinsts := ← e.pfinsts.mapM (fun (i,k,ks) => do return (i,← expr p bs k,← ks.mapM (expr p bs)))}

/-- Covers use the integrand's map layout; whole-address integrands remain
unchanged. A mixed-arity integrand is unsupported, never guessed. -/
def sumArity (p : Plan) (g : E) : Except Error (Option Nat) := do
  let arities := (mapsE g).filterMap (layout p)
  match arities with
  | [] => return none
  | n :: ns => if ns.all (· == n) then return some n else throw (.syntax (.unsupportedKey n))

def target (p : Plan) (old : SumMachine) : Except Error SumMachine := do
  let base ← RadixCertificateTransport.liftSyntax (RadixTupleSyntax.machine (config p) old.s)
  let sums ← old.sums.mapM fun d => do
    let n ← sumArity p d.g
    let cs ← d.cs.mapM fun k => RadixCertificateTransport.liftSyntax
      (match n with | some n => rekey p.radix n [] k | none => expr p [] k)
    return {d with cs := cs}
  return ⟨base,sums⟩

/-- Fresh indices use an arity-dependent prefix sum, not a fixed stride. -/
def prepare (p : Plan) (ps : List SEntry) : Except Error (List RadixCertificateTransport.Prepared) := do
  let mut fresh := p.freshBase
  let mut result := []
  for (e,i) in ps.zipIdx do
    let next ← RadixCertificateTransport.prepare p.layouts fresh 0 e
    let width := match next.profile with | some (_,n) => n-1 | none => 0
    result := result ++ [{next with profile := next.profile.map (fun (_,n) => (i,n))}]
    fresh := fresh + width
  return result

def translate (p : Plan) (old : SumMachine) (ps : List SEntry) : Except Error (SumMachine × List SEntry) := do
  let t ← target p old
  let prepared ← prepare p ps
  let bs := prepared.flatMap (·.bindings)
  let profiles := prepared.filterMap (·.profile)
  let es ← prepared.mapM (fun x => RadixCertificateTransport.liftSyntax (entry p profiles bs x.entry))
  let proof ← es.mapM fun e => do
    let start ← certificate p bs (sStartGoal t.plain e) e.start
    let step ← certificate p bs (sStepGoal t.plain es e) e.step
    return {e with start := start, step := step}
  return (t,proof)

/-- Candidate success is not a validity-preservation axiom. -/
theorem checked (t : SumMachine) (ps : List SEntry) (h : checkSMachine t.plain ps = true) :
    ∀ ρ M, SReach t.plain ρ M → ∀ e ∈ ps, e.Holds ρ M := smachine_sound _ _ h
#print axioms checked
end Bapa.RadixSumTransport
