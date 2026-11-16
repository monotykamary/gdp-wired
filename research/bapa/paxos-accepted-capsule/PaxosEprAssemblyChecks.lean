import PaxosEprFamilyAssembly
namespace Bapa.PaxosEprFamilyAssembly
open Kern Lean Bapa.PaxosEprTreeRepairChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
#eval (show IO Unit from do
 let out := (← IO.getEnv "SUPERCOMPUTER_OUTPUT_DIR").getD "."
 let .ok ps := buildFamily | throw (IO.userError "family syntax refused")
 let s := PaxosEprTarget.machine
 let ds := PaxosEprTarget.declarations
 let es := ps.map (·.e)
 let rows := ps.zipIdx.flatMap (fun (ce,i) => [
   Json.mkObj [("law",toJson i),("step",toJson false),("checked",toJson (checkMC (cStartGoal s ds ce.e) (cStartDecls s ds) ce.start))],
   Json.mkObj [("law",toJson i),("step",toJson true),("checked",toJson (checkMC (cStepGoal s ds es ce.e) (cStepDecls s ds) ce.step))]])
 IO.FS.writeFile (out ++ "/ASSEMBLY-CHECKS.json") ((ja rows).compress ++ "\n")
 IO.FS.writeFile (out ++ "/FAMILY-STATUS.json") ((Json.mkObj [
  ("entries",toJson ps.length),("completeNativeCountedGate",toJson (checkCMachine s ds ps)),
  ("installedTrees",toJson installedTrees),("pendingSteps",toJson pendingSteps),("sourceAccepted",toJson false)]).compress ++ "\n")
 for i in installedTrees do
  IO.FS.writeFile (out ++ s!"/PaxosEprAssemblyCheck{i}.lean")
   ("import PaxosEprFamilyAssembly\nnamespace Bapa.PaxosEprFamilyAssembly\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n" ++
    s!"theorem assembled_step_{i} : checkedAt {i} true = true := by decide +kernel\n#print axioms assembled_step_{i}\nend Bapa.PaxosEprFamilyAssembly\n"))
end Bapa.PaxosEprFamilyAssembly
