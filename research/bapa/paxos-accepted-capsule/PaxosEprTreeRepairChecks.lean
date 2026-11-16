import Proofs
import PaxosEprAdapterNamed
import PaxosEprTreeRepair
import Lean
open Kern Lean Cert
namespace Bapa.PaxosEprTreeRepairChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

-- Exact baseline context from the frozen AdapterAudit; no family evaluation.
def source := captured_paxos_epr_0_checkedMachine
def retained := captured_paxos_epr_0_proof
def oldDecls := captured_paxos_epr_0_decls
def layouts : List (Nat × Nat) := [(1,2),(2,2),(3,2),(4,3),(5,2),(11,2),(12,2),(16,2),(17,2)]
def prepared := retained.zipIdx.map (fun (ce,i) => RadixCertificateTransport.prepare layouts 1000000 i ce.e)
def bindings : List RadixKeySyntax.RawAddress :=
  (prepared.filterMap (fun r => r.toOption)).flatMap (·.bindings) ++
  RadixCertificateTransport.everyBindings layouts source ++
  [⟨133,2,[.var 133,.var 2000000]⟩,⟨84,2,[.var 84,.var 2000001]⟩,⟨29,2,[.var 29,.var 2000002]⟩]
def profiles := (prepared.filterMap (fun r => r.toOption)).filterMap (·.profile)
def config : PaxosEprAdapterSyntax.Config := ⟨64,layouts,bindings,some 1⟩
def targetMachine := PaxosEprAdapterSyntax.machine config source
def targetDecls := oldDecls.zipIdx.mapM (fun (d,i) => PaxosEprAdapterSyntax.atField s!"decls[{i}]" (PaxosEprAdapterSyntax.declaration config d))
def targetEntries : Except String (List SEntry) := prepared.zipIdx.mapM fun (p,i) => do
  let p ← p.mapError (fun e => s!"entry[{i}].binder: {reprStr e}")
  (PaxosEprAdapterSyntax.entry config profiles p.entry).mapError (fun e => s!"entry[{i}]: {reprStr e}")

def node (s : String) (xs : List Json) : Json := Json.arr ((Json.str s :: xs).toArray)
def ja (xs : List Json) : Json := Json.arr xs.toArray
def jn (n : Nat) : Json := toJson n
mutual
 def je : E → Json
  | .var n => node "var" [jn n] | .const n => node "const" [jn n]
  | .add a b => node "add" [je a,je b] | .sub a b => node "sub" [je a,je b]
  | .mul n a => node "mul" [jn n,je a] | .prod a b => node "prod" [je a,je b]
  | .min a b => node "min" [je a,je b] | .max a b => node "max" [je a,je b]
  | .ite c a b => node "ite" [jc c,je a,je b]
  | .get m a => node "get" [jn m,je a] | .tup a b => node "tup" [je a,je b]
  | .proj i a => node "proj" [jn i,je a]
 def jc : C → Json
  | .le a b => node "le" [je a,je b] | .lt a b => node "lt" [je a,je b]
  | .eq a b => node "eq" [je a,je b]
  | .and a b => node "and" [jc a,jc b] | .or a b => node "or" [jc a,jc b]
  | .not a => node "not" [jc a]
end

def jr (r : Cert.Row) : Json := Json.mkObj [("coefs",toJson r.coefs),("const",toJson r.const)]
def jrs (rs : List Cert.Row) : Json := ja (rs.map jr)
def js : Src → Json
 | .atom n => node "atom" [jn n] | .fact n => node "fact" [jn n]
 | .nat n => node "nat" [jn n] | .eq n => node "eq" [jn n]
 | .term n => node "term" [jn n] | .any => node "any" []
def jv : VDef → Json
 | .var n => node "var" [jn n] | .term e => node "term" [je e]
 | .cell m r => node "cell" [jn m,jr r] | .cellT m rs => node "cellT" [jn m,jrs rs]
 | .mono ns => node "mono" [toJson ns]
def jp (p : Path) : Json := ja (p.reverse.map fun a => Json.mkObj [("row",jr a.1),("yes",toJson a.2)])
def jstep : Cert.Step → Json
 | .input i => node "input" [jn i]
 | .combine i j a b => node "combine" [jn i,jn j,toJson a,toJson b]
 | .cut i g q c => node "cut" [jn i,toJson g,toJson q,toJson c]
def jt : Tree → Json
 | .split r y n => node "split" [jr r,jt y,jt n]
 | .leaf rs ss eqs prods => node "leaf" [jrs rs,ja (ss.map jstep),toJson eqs,toJson prods]
 | .leafAt rs ss eqs prods => node "leafAt" [ja (rs.map fun p => ja [jr p.1,js p.2]),ja (ss.map jstep),toJson eqs,toJson prods]
 | .leafSq rs sqs ss eqs prods => node "leafSq" [ja (rs.map fun p => ja [jr p.1,js p.2]),jrs sqs,ja (ss.map jstep),toJson eqs,toJson prods]

def context (ds : List CDecl) (k : CCert) : Option (List C) := do
 let cs ← toCounts ds k.reads
 let hs ← countHyps cs k.insts
 return k.hyps ++ k.reads.map (readHyp ds) ++ pickHyps ds k.reads k.picks ++ hs

def selected : List Bool → Tree → Path → Option (Path × Tree)
 | [],t,p => some (p,t)
 | b::bs,.split r y n,p => selected bs (if b then y else n) ((r,b)::p)
 | _,_,_ => none

def pathFor (i : Nat) : List Bool :=
 if i == 4 || i == 5 then [true,true]
 else if i == 19 || i == 22 then [true,false]
 else [true,true,true,true,true,true,true,true,false,false,false,true,true,true,true,true]

def leafData (k : CCert) (hs : List C) (dirs : List Bool) (initial : Path := []) : Json :=
 match selected dirs k.tree initial with
 | none => node "missing" []
 | some (p,t) =>
   let p := lemmaPath k.lemmas p
   let rows := match t with | .leafAt rs _ _ _ | .leafSq rs _ _ _ _ => rs | .leaf rs _ _ _ => rs.map (fun r => (r,Src.any)) | _ => []
   let eqs := match t with | .leafAt _ _ es _ | .leafSq _ _ _ es _ | .leaf _ _ es _ => es | _ => []
   Json.mkObj [("path",jp p),("leaf",jt t),
    ("rowObservations",ja (rows.map fun (r,s) => Json.mkObj [
      ("row",jr r),("source",js s),("sourceRows",jrs (srcRows k.tab p hs eqs s)),
      ("fallbackAvailable",toJson ((leafRows k.tab p hs eqs).any (same r)))])),
    ("facts",ja (hs.zipIdx.map fun (h,i) => Json.mkObj [("index",jn i),("condition",jc h),("truth",toJson (truth k.tab p h)),("rows",jrs (facts k.tab p true h))]))]

def run : IO Unit := do
 let out := (← IO.getEnv "SUPERCOMPUTER_OUTPUT_DIR").getD "."
 let .ok s := targetMachine | throw (IO.userError "target machine refused")
 let .ok ds := targetDecls | throw (IO.userError "target declarations refused")
 let .ok es := targetEntries | throw (IO.userError "target entries refused")
 for i in ([4,5,19,21,22] : List Nat) do
  let some ce := retained[i]? | throw (IO.userError "retained entry missing")
  let some e := es[i]? | throw (IO.userError "target entry missing")
  let .ok k := PaxosEprAdapterCertificate.certificate config ce.step | throw (IO.userError "certificate construction refused")
  let some hs := context (cStepDecls s ds) k | throw (IO.userError "target count context refused")
  let some oldhs := context (cStepDecls source oldDecls) ce.step | throw (IO.userError "old count context refused")
  let result := Json.mkObj [("law",jn i),("path",toJson (pathFor i)),
    ("old",leafData ce.step oldhs (pathFor i)),("new",leafData k hs (pathFor i)),
    ("oldTable",ja (ce.step.tab.map jv)),("newTable",ja (k.tab.map jv)),
    ("oldTree",jt ce.step.tree),("newTree",jt k.tree),
    ("goal",ja ((cStepGoal s ds es e).map jc)),
    ("named",ja (k.hyps.map jc)),("lemmas",jn k.lemmas.length),
    ("certificateChecks",jn 0),("safetyClaim",toJson false)]
  IO.FS.writeFile (out ++ s!"/STEP-{i}.json") (result.compress ++ "\n")
def build (i : Nat) : Except String (List C × List CDecl × CCert) := do
 let s ← targetMachine.mapError (fun e => reprStr e)
 let ds ← targetDecls.mapError (fun e => reprStr e)
 let es ← targetEntries
 let some ce := retained[i]? | throw "missing retained entry"
 let some e := es[i]? | throw "missing target entry"
 let names ← (PaxosEprAdapterNamed.hypotheses profiles source s oldDecls ds (retained.map (·.e)) es ce.e e true ce.step).mapError (fun e => reprStr e)
 let k ← (PaxosEprAdapterCertificate.certificate config ce.step (some names)).mapError (fun e => reprStr e)
 let goal := cStepGoal s ds es e
 let cds := cStepDecls s ds
 let repaired ← PaxosEprTreeRepair.repair i goal cds k
 return (goal,cds,repaired)

def candidateChecked (i : Nat) : Bool :=
 match build i with | .ok (goal,ds,k) => checkMC goal ds k | .error _ => false

def firstFailed (tab : List VDef) (hs : List C) (lemmas : List CutLemma) (p : Path) : Tree → Path × Tree
 | .split r y n =>
   if checkTLemmas tab hs lemmas ((r,true)::p) y then firstFailed tab hs lemmas ((r,false)::p) n
   else firstFailed tab hs lemmas ((r,true)::p) y
 | t => (p,t)

def checkRun : IO Unit := do
 let out := (← IO.getEnv "SUPERCOMPUTER_OUTPUT_DIR").getD "."
 let mut results : List Json := []
 let mut proofs : List String := []
 for i in ([4,5,19,21,22] : List Nat) do
  match build i with
  | .error err =>
    results := results ++ [Json.mkObj [("law",jn i),("error",toJson err),("checked",toJson false)]]
  | .ok (goal,ds,k) =>
    let checked := checkMC goal ds k
    let some hs := context ds k | throw (IO.userError "count context disappeared")
    let failure := if checked then Json.null else
      let (p,t) := firstFailed k.tab hs k.lemmas [] k.tree
      Json.mkObj [("path",jp p),("leaf",jt t),
        ("details",leafData {k with tree := t} hs [] p)]
    let record := Json.mkObj [("law",jn i),("checked",toJson checked),("failure",failure),("tree",jt k.tree)]
    IO.FS.writeFile (out ++ s!"/CHECK-{i}.json") (record.compress ++ "\n")
    results := results ++ [Json.mkObj [("law",jn i),("checked",toJson checked)]]
    proofs := proofs ++ [s!"theorem checked_{i} : candidateChecked {i} = {if checked then "true" else "false"} := by decide +kernel\n#print axioms checked_{i}\n"]
 IO.FS.writeFile (out ++ "/CHECKS.json") ((ja results).compress ++ "\n")
 IO.FS.writeFile (out ++ "/P1PaxosTreeVerdicts.lean")
  ("import PaxosEprTreeRepairChecks\nnamespace Bapa.PaxosEprTreeRepairChecks\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n" ++ String.join proofs ++ "end Bapa.PaxosEprTreeRepairChecks\n")
#eval (show IO Unit from do
 if (← IO.getEnv "PAXOS_TREE_MODE") == some "check" then checkRun else run)
end Bapa.PaxosEprTreeRepairChecks
