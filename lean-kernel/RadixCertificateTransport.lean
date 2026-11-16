import RadixTupleSyntax
import RadixEqualityTree
import CertificateBooleanCleanup

/-! General, fail-closed composition of the typed key, binder, table and tree
phases. The result is a candidate. Only a complete checkSMachine result gives a
family theorem; there is no unconditional claim that fixed-radix certificates
survive re-keying. The original source bridge is a separate obligation. -/
namespace Bapa.RadixCertificateTransport
open Kern

inductive Error where
  | binder (index : Nat)
  | syntax (reason : RadixKeySyntax.Error)
  | table (reason : RadixCertificateTable.Error)
  | obligation (index : Nat) (phase reason : String)
  deriving Repr

structure Prepared where
  entry : SEntry
  profile : Option (Nat × Nat) := none
  bindings : List RadixKeySyntax.RawAddress := []

def prepare (layouts : List (Nat × Nat)) (freshBase index : Nat) (e : SEntry) : Except Error Prepared := do
  match e.law.key with
  | none => return ⟨e,none,[]⟩
  | some v =>
    let uses := RadixBinderExpansion.inspectC layouts v e.law.holds
    match uses.arities.head? with
    | none => return ⟨e,none,[]⟩
    | some arity =>
      let fresh := (List.range (arity-1)).map (fun i => freshBase + index*16+i)
      match RadixBinderExpansion.expandCandidate layouts fresh e with
      | none => throw (.binder index)
      | some p => return ⟨p.candidate,some (index,arity),[p.lawAddress,p.skolemAddress]⟩

def liftSyntax {α : Type} : Except RadixKeySyntax.Error α → Except Error α
  | .ok x => .ok x
  | .error e => .error (.syntax e)

def liftTable {α : Type} : Except RadixCertificateTable.Error α → Except Error α
  | .ok x => .ok x
  | .error e => .error (.table e)

def atObligation {α : Type} (index : Nat) (phase : String) : Except Error α → Except Error α
  | .ok x => .ok x
  | .error e => .error (.obligation index phase (reprStr e))

def translatedTableExpr (cfg : RadixTupleSyntax.Config) (e : E) :
    Except RadixCertificateTable.Error E :=
  match RadixTupleSyntax.expr cfg e with
  | .ok e => .ok e
  | .error e => .error (.key e)

/-- Keep the actual target goal, not an invented replacement hypothesis list.
An empty named list tells checkIn to use its own complete generated goal. -/
def certificate (cfg : RadixTupleSyntax.Config) (cleanup : Bool) (goal : List C)
    (k : Kern.Cert) : Except Error Kern.Cert := do
  let tab ← liftTable (RadixCertificateTable.table cfg.radix cfg.layouts cfg.bindings
    (translatedTableExpr cfg) k.1)
  let shift := (RadixCertificateTable.freshVariables k.1 cfg.bindings).length
  let plans := RadixEqualityTree.plans shift k.1 tab
  let bound := if cfg.sizeVariable.isNone then some cfg.radix else none
  let candidate : Kern.Cert :=
    (tab,[],RadixEqualityTree.tree shift bound plans [] k.2.2)
  return if cleanup then CertificateBooleanCleanup.certificate goal candidate else candidate

/-- Whole-address every binders remain bound variables, represented in the
body by explicit projection components; they do not become free parameters. -/
def everyBindings (layouts : List (Nat × Nat)) (s : SMachine) : List RadixKeySyntax.RawAddress :=
  s.every.filterMap fun p =>
    (RadixBinderExpansion.mapArity layouts p.1).map fun arity =>
      ⟨p.2.1,arity,RadixTupleSyntax.projectionParts arity (.var p.2.1)⟩

def translate (layouts : List (Nat × Nat)) (freshBase : Nat) (cleanup : Bool)
    (s : SMachine) (ps : List SEntry) : Except Error (SMachine × List SEntry) := do
  let prepared ← ps.zipIdx.mapM (fun (e,i) => prepare layouts freshBase i e)
  let profiles := prepared.filterMap (·.profile)
  let bindings := prepared.flatMap (·.bindings) ++ everyBindings layouts s
  let cfg : RadixTupleSyntax.Config := ⟨64,layouts,bindings,none⟩
  let machine ← liftSyntax (RadixTupleSyntax.machine cfg s)
  let entries ← prepared.zipIdx.mapM (fun (p,i) =>
    atObligation i "syntax" (liftSyntax (RadixTupleSyntax.entrySyntax cfg profiles [] p.entry)))
  let proof ← entries.zipIdx.mapM fun (e,i) => do
    let start ← atObligation i "init" (certificate cfg cleanup (sStartGoal machine e) e.start)
    let step ← atObligation i "step" (certificate cfg cleanup (sStepGoal machine entries e) e.step)
    return {e with start := start, step := step}
  return (machine,proof)

/-- The same complete trusted gate is mandatory after every translation. -/
theorem checked (layouts : List (Nat × Nat)) (freshBase : Nat) (cleanup : Bool)
    (s : SMachine) (ps : List SEntry) (s' : SMachine) (ps' : List SEntry)
    (_translated : translate layouts freshBase cleanup s ps = .ok (s',ps'))
    (h : checkSMachine s' ps' = true) :
    ∀ ρ M, SReach s' ρ M → ∀ e ∈ ps', e.Holds ρ M := smachine_sound _ _ h

#print axioms checked
end Bapa.RadixCertificateTransport
