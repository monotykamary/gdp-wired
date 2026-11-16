import PaxosEprTreeRepairChecks
import PaxosEprTreesRepair
namespace Bapa.PaxosEprTreesChecks
open Kern Lean
open PaxosEprTreeRepairChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def build (i : Nat) : Except String (List C × List CDecl × CCert) := do
 let s ← targetMachine.mapError (fun e => reprStr e)
 let ds ← targetDecls.mapError (fun e => reprStr e)
 let es ← targetEntries
 let some ce := retained[i]? | throw "missing retained entry"
 let some e := es[i]? | throw "missing target entry"
 let names ← (PaxosEprAdapterNamed.hypotheses profiles source s oldDecls ds (retained.map (·.e)) es ce.e e true ce.step).mapError (fun e => reprStr e)
 let k ← (PaxosEprAdapterCertificate.certificate config ce.step (some names)).mapError (fun e => reprStr e)
 let goal := cStepGoal s ds es e
 let repaired ← PaxosEprTreesRepair.repair i goal (cStepDecls s ds) k
 return (goal,cStepDecls s ds,repaired)

def candidateChecked (i : Nat) : Bool :=
 match build i with | .ok (goal,ds,k) => checkMC goal ds k | .error _ => false

def run : IO Unit := do
 let out := (← IO.getEnv "SUPERCOMPUTER_OUTPUT_DIR").getD "."
 let mut results : List Json := []
 let mut proofs : List String := []
 let selected := (← IO.getEnv "PAXOS_LAW").bind String.toNat?
 for i in ([7,9,10,13,14,15,16,18,20,23,24] : List Nat).filter (fun i => selected.isNone || selected == some i) do
  match build i with
  | .error err =>
    results := results ++ [Json.mkObj [("law",jn i),("error",toJson err),("checked",toJson false)]]
  | .ok (goal,ds,k) =>
    let checked := checkMC goal ds k
    let some hs := context ds k | throw (IO.userError "count context disappeared")
    let failure := if checked then Json.null else
      let (p,t) := firstFailed k.tab hs k.lemmas [] k.tree
      Json.mkObj [("path",jp p),("leaf",jt t),("details",leafData {k with tree := t} hs [] p),("nextTest",match PaxosEprTreesRepair.missingTest k.tab hs (lemmaPath k.lemmas p) t with | some r => jr r | none => Json.null)]
    IO.FS.writeFile (out ++ s!"/CHECK-{i}.json") ((Json.mkObj [("law",jn i),("checked",toJson checked),("failure",failure),("tree",jt k.tree),("table",ja (k.tab.map jv))]).compress ++ "\n")
    results := results ++ [Json.mkObj [("law",jn i),("checked",toJson checked)]]
    proofs := proofs ++ [s!"theorem checked_{i} : candidateChecked {i} = {if checked then "true" else "false"} := by decide +kernel\n#print axioms checked_{i}\n"]
 IO.FS.writeFile (out ++ "/CHECKS.json") ((ja results).compress ++ "\n")
 IO.FS.writeFile (out ++ "/PaxosEprTreesVerdicts.lean")
  ("import PaxosEprTreesChecks\nnamespace Bapa.PaxosEprTreesChecks\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n" ++ String.join proofs ++ "end Bapa.PaxosEprTreesChecks\n")
end Bapa.PaxosEprTreesChecks
