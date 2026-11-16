import Proofs
import RadixCertificateTransport
import BoundErasureReplay

/-! Lock-specific adapter. No search and no finite-subsum replacement.
The SUM integrands remain reads over all encoded natural addresses; only
actual Message write/cover addresses change from radix64 to tuple keys. -/
namespace Bapa.SimpleDecentralizedLockTransport
open Kern
deriving instance Repr for E, C
deriving instance Repr for MMachine
deriving instance Repr for FMMachine
deriving instance Repr for MLaw
deriving instance Repr for SMachine
deriving instance Repr for VDef
deriving instance Repr for Src
deriving instance Repr for Tree
deriving instance Repr for SEntry
deriving instance Repr for SumDecl
deriving instance Repr for SumMachine
deriving instance DecidableEq for E, C
deriving instance DecidableEq for Cert.Row
deriving instance DecidableEq for Cert.Step
deriving instance DecidableEq for MLaw
deriving instance DecidableEq for VDef
deriving instance DecidableEq for Src
deriving instance DecidableEq for Tree
deriving instance DecidableEq for SEntry
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def literal {α : Type} [Repr α] (value : α) : String := (reprStr value).replace "\n" " "

def layouts : List (Nat × Nat) := [(0,2)]
def config : RadixTupleSyntax.Config := ⟨64,layouts,[],none⟩
def sumOutcome : Except RadixKeySyntax.Error SumMachine := do
  let old := captured_simple_decentralized_lock_0_sums
  let base ← RadixTupleSyntax.machine config old.s
  let sums ← old.sums.mapM fun d => do
    return {d with cs := ← d.cs.mapM (fun key => if d.v == 5 then RadixKeySyntax.rekey 64 2 [] key else RadixTupleSyntax.expr config key)}
  return ⟨base,sums⟩

def target : SumMachine := match sumOutcome with
  | .ok h => h
  | .error _ => captured_simple_decentralized_lock_0_sums

-- Opaque raw addresses stay natural-valued in the exact SUM layer. Only the
-- typed Message kind binder is expanded; arbitrary extra instances may use
-- decoded components, but never become assumptions about those components.
def address (bs : List RadixKeySyntax.RawAddress) (e : E) : Except RadixKeySyntax.Error E :=
  match e with
  | .var v => if bs.any (fun b => b.variableId == v) then RadixKeySyntax.rekey 64 2 bs e else .ok e
  | _ => RadixKeySyntax.rekey 64 2 bs e
mutual
  def expr (bs : List RadixKeySyntax.RawAddress) : E → Except RadixKeySyntax.Error E
    | .var v => .ok (.var v)
    | .const n => .ok (.const n)
    | .get m k => do return .get m (← if m == 0 then address bs k else expr bs k)
    | .add a b => do return .add (← expr bs a) (← expr bs b)
    | .sub a b => do return .sub (← expr bs a) (← expr bs b)
    | .mul n a => do return .mul n (← expr bs a)
    | .min a b => do return .min (← expr bs a) (← expr bs b)
    | .max a b => do return .max (← expr bs a) (← expr bs b)
    | .prod a b => do return .prod (← expr bs a) (← expr bs b)
    | .ite c a b => do return .ite (← cond bs c) (← expr bs a) (← expr bs b)
    | .tup a b => do return .tup (← expr bs a) (← expr bs b)
    | .proj n a => do return .proj n (← expr bs a)
  def cond (bs : List RadixKeySyntax.RawAddress) : C → Except RadixKeySyntax.Error C
    | .lt a b => do return .lt (← expr bs a) (← expr bs b)
    | .le a b => do return .le (← expr bs a) (← expr bs b)
    | .eq a b => do
      if (RadixTupleSyntax.rawArity {config with bindings := bs} a).isSome ||
          (RadixTupleSyntax.rawArity {config with bindings := bs} b).isSome then
        return .eq (← address bs a) (← address bs b)
      return .eq (← expr bs a) (← expr bs b)
    | .and a b => do return .and (← cond bs a) (← cond bs b)
    | .or a b => do return .or (← cond bs a) (← cond bs b)
    | .not a => do return .not (← cond bs a)
end

def isOpaque (bs : List RadixKeySyntax.RawAddress) (tab : List VDef) (r : Cert.Row) : Bool :=
  match r.coefs with
  | [(j,1)] => r.const == 0 && (match tab[j]? with
      | some (.var v) => !(bs.any (fun b => b.variableId == v))
      | _ => false)
  | _ => false

def table (bs : List RadixKeySyntax.RawAddress) (old : List VDef) : Except RadixCertificateTable.Error (List VDef) := do
  let fresh := (RadixCertificateTable.freshVariables old bs).map VDef.var
  let shift := fresh.length
  let moved ← old.mapM fun d => do
    match d with
    | .var v => pure (.var v)
    | .mono js => pure (.mono (js.map (·+shift)))
    | .term e => match expr bs (CertificateBoundErasure.expr 64 e) with
      | .ok e' => pure (.term e')
      | .error error => throw (.key error)
    | .cell m k => if m != 0 || isOpaque bs old k then pure (.cell m (RadixCertificateTable.row shift k)) else
        return .cellT m (← RadixCertificateTable.components 64 2 bs old fresh k)
    | .cellT m ks => pure (.cellT m (ks.map (RadixCertificateTable.row shift)))
  return fresh ++ moved

def certificate (bs : List RadixKeySyntax.RawAddress) (goal : List C) (k : Kern.Cert) : Except RadixCertificateTransport.Error Kern.Cert := do
  let tab ← RadixCertificateTransport.liftTable (table bs k.1)
  let shift := tab.length-k.1.length
  let plans := RadixEqualityTree.plans shift k.1 tab
  let candidate := (tab,[],RadixEqualityTree.tree shift (some 64) plans [] k.2.2)
  return CertificateBooleanCleanup.certificate goal candidate

def instanceParts (bs : List RadixKeySyntax.RawAddress) (e : E) : Except RadixKeySyntax.Error (List E) :=
  match e with
  | .var v => if bs.any (fun b => b.variableId == v) then RadixKeySyntax.keyParts 64 bs 2 e
      else .ok (RadixTupleSyntax.projectionParts 2 e)
  | _ => RadixKeySyntax.keyParts 64 bs 2 e

def entry (bs : List RadixKeySyntax.RawAddress) (e : SEntry) : Except RadixKeySyntax.Error SEntry := do
  let mut one := []
  let mut many := []
  for (i,k) in e.insts do
    if i == 0 then
      let parts ← instanceParts bs k
      match parts with
      | [a,b] => many := many ++ [(i,a,[b])]
      | _ => throw (.unsupportedKey 2)
    else one := one ++ [(i,← expr bs k)]
  for (i,k,ks) in e.pinsts do
    if i == 0 then
      let parts ← instanceParts bs k
      match parts with
      | [a,b] => many := many ++ [(i,a,[b] ++ (← ks.mapM (expr bs)))]
      | _ => throw (.unsupportedKey 2)
    else many := many ++ [(i,← expr bs k,← ks.mapM (expr bs))]
  return {e with
    law := {e.law with holds := ← cond bs (CertificateBoundErasure.condition 64 e.law.holds)}
    insts := one, pinsts := many
    qinsts := ← e.qinsts.mapM (fun (i,ks) => do return (i,← ks.mapM (fun k => if i == 19 then address bs k else expr bs k)))
    finsts := ← e.finsts.mapM (fun (i,k) => do return (i,← expr bs k))
    pfinsts := ← e.pfinsts.mapM (fun (i,k,ks) => do return (i,← expr bs k,← ks.mapM (expr bs)))}

def outcome : Except RadixCertificateTransport.Error (List SEntry × List (List (List VDef × Tree))) := do
  let prepared ← captured_simple_decentralized_lock_0_proof.zipIdx.mapM (fun (e,i) => RadixCertificateTransport.prepare layouts 1000000 i e)
  let bs := prepared.flatMap (·.bindings)
  let entries ← prepared.mapM (fun p => RadixCertificateTransport.liftSyntax (entry bs p.entry))
  let proof ← entries.mapM fun e => do
    return {e with
      start := ← certificate bs (sStartGoal target.plain e) e.start
      step := ← certificate bs (sStepGoal target.plain entries e) e.step}
  let covers ← (target.sums.zip captured_simple_decentralized_lock_0_covers).mapM fun (d,ks) =>
    ((coverWs target.s d).zip ks).mapM fun (w,k) => do
      let c ← certificate bs (sumCoverGoal target.s proof d w) (k.1,[],k.2)
      return (c.1,c.2.2)
  return (proof,covers)

def machine := target.plain
def proof : List SEntry := match outcome with | .ok p => p.1 | .error _ => []
def covers : List (List (List VDef × Tree)) := match outcome with | .ok p => p.2 | .error _ => []

-- Keep the complete four-entry family, deleting only the public step certificate.
-- An empty family alone is vacuously checked and is not a deletion control.
def withoutPublicCertificate : List SEntry := proof.zipIdx.map fun (e,i) =>
  if i == 2 then {e with step := (e.step.1,[],.leaf [] [] [] [])} else e

def genericOutcome := RadixCertificateTransport.translate layouts 1000000 true
  captured_simple_decentralized_lock_0_machine captured_simple_decentralized_lock_0_proof

def targetSucceeded : Bool := match sumOutcome with | .ok _ => true | .error _ => false

theorem target_created : targetSucceeded = true := by decide +kernel
theorem target_sum_wellformed : sumOk target = true := by decide +kernel
theorem exact_integrands_preserved : target.sums.map (·.g) =
    captured_simple_decentralized_lock_0_sums.sums.map (·.g) := by decide +kernel
theorem message_cover_rekeyed : (target.sums[1]'(by decide)).cs =
    [.tup (.var 1) (.var 2)] := by decide +kernel

#eval (show IO Unit from do
  let out := (← IO.getEnv "SUPERCOMPUTER_OUTPUT_DIR").getD "."
  let report := match genericOutcome with
    | .error e => "GENERIC_TRANSLATION_REFUSED: " ++ reprStr e
    | .ok (_,ps) => "CANDIDATE_ONLY: " ++ reprStr (BoundErasureReplay.plainChecks target.plain ps)
  IO.FS.writeFile (out ++ "/SDL-DIAGNOSTIC.txt") (report ++ "\nSOURCE_BRIDGE_PENDING\n")
  IO.println report
  IO.FS.writeFile (out ++ "/SdlTargetData.lean")
    ("import SimpleDecentralizedLockTransport\nopen Kern\ndef sdl_target_data : SMachine := " ++ literal target.s ++
    "\ntheorem sdl_target_eq : Bapa.SimpleDecentralizedLockTransport.target.s = sdl_target_data := by rfl\n#print axioms sdl_target_eq\n")
  match outcome with
  | .error e =>
    IO.FS.writeFile (out ++ "/SDL-ADAPTER-ERROR.txt") (reprStr e ++ "\n")
    throw (IO.userError (reprStr e))
  | .ok (ps,cs) =>
    IO.FS.writeFile (out ++ "/SdlCandidateData.lean")
      ("import SimpleDecentralizedLockTransport\nopen Kern\nnamespace Bapa.SdlConcrete\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n" ++
       "def target : SumMachine := " ++ literal target ++
       "\ndef machine : SMachine := target.plain\ndef proof : List SEntry := " ++ literal ps ++
       "\ndef covers : List (List (List VDef × Tree)) := " ++ literal cs ++
       "\ndef withoutPublicCertificate : List SEntry := proof.zipIdx.map fun (e,i) => if i == 2 then {e with step := (e.step.1,[],.leaf [] [] [] [])} else e\n" ++
       "theorem target_eq : Bapa.SimpleDecentralizedLockTransport.target = target := by rfl\n" ++
       "theorem proof_eq : Bapa.SimpleDecentralizedLockTransport.proof = proof := by decide +kernel\n" ++
       "theorem covers_eq : Bapa.SimpleDecentralizedLockTransport.covers = covers := by decide +kernel\n" ++
       "#print axioms target_eq\n#print axioms proof_eq\n#print axioms covers_eq\nend Bapa.SdlConcrete\n")
    BoundErasureReplay.emitPlain out "SdlCandidateData"
      "Bapa.SdlConcrete" target.plain ps 2
    let checked := checkSums target ps cs
    let deleted := checkSums target ps [[],[]]
    let missing := checkSMachine target.plain withoutPublicCertificate
    IO.FS.writeFile (out ++ "/SDL-SUM-CHECK.txt") s!"cover={checked}\ndeleted={deleted}\nmissing={missing}\n"
    IO.FS.writeFile (out ++ "/SumChecks.lean")
      s!"import SdlCandidateData\nopen Kern\nnamespace Bapa.SdlConcrete.Checked\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ntheorem cover : checkSums target proof covers = {checked} := by decide +kernel\n#print axioms cover\ntheorem deleted : checkSums target proof [[],[]] = {deleted} := by decide +kernel\n#print axioms deleted\ntheorem missing_certificate : checkSMachine target.plain withoutPublicCertificate = {missing} := by decide +kernel\n#print axioms missing_certificate\nend Bapa.SdlConcrete.Checked\n")
#print axioms target_created
#print axioms target_sum_wellformed
#print axioms exact_integrands_preserved
#print axioms message_cover_rekeyed
end Bapa.SimpleDecentralizedLockTransport
