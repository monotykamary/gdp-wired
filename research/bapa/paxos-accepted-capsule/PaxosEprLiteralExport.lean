import PaxosEprFamilyAssembly
import PaxosEprCountedGate
namespace Bapa.PaxosEprLiteralExport
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0
deriving instance Repr for E, C, VDef, Src, Tree, MLaw, SEntry, CInst, CutLemma, CCert, CEntry
#eval (show IO Unit from do
 let out := (← IO.getEnv "SUPERCOMPUTER_OUTPUT_DIR").getD "."
 let .ok ps := PaxosEprFamilyAssembly.buildFamily | throw (IO.userError "assembly refused")
 unless checkCMachine PaxosEprTarget.machine PaxosEprTarget.declarations ps do
  throw (IO.userError "complete native family gate refused")
 let header := "import PaxosEprCountedGate\nnamespace Bapa.PaxosEprLiteral\nopen Kern Bapa.PaxosEprCountedGate\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
 let defs := String.join (ps.zipIdx.map (fun (ce,i) => s!"def entry{i} : CEntry :=\n{reprStr ce}\n"))
 let names := (List.range ps.length).map (fun i => s!"entry{i}")
 let family := "def family : List CEntry := [" ++ String.intercalate "," names ++ "]\n"
 let exact := "deriving instance DecidableEq for Cert.Row, Cert.Step, VDef, Src, Tree, SEntry\nderiving instance DecidableEq for Except\ntheorem entries_exact : PaxosEprTreeRepairChecks.targetEntries = .ok (family.map (·.e)) := by decide +kernel\n#print axioms entries_exact\n"
 IO.FS.writeFile (out++"/PaxosEprLiteralFamily.lean") (header++defs++family++exact++"end Bapa.PaxosEprLiteral\n")
 let proofHeader := "import PaxosEprLiteralFamily\nnamespace Bapa.PaxosEprLiteral\nopen Kern Bapa.PaxosEprCountedGate\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
 IO.FS.writeFile (out++"/PaxosEprLiteralGlobal.lean") (proofHeader++"theorem global_checked : globalGate PaxosEprTarget.machine PaxosEprTarget.declarations family = true := by decide +kernel\n#print axioms global_checked\nend Bapa.PaxosEprLiteral\n")
 for i in List.range ps.length do
  IO.FS.writeFile (out++s!"/PaxosEprLiteralEntry{i}.lean") (proofHeader++s!"theorem entry{i}_checked : entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry{i} = true := by decide +kernel\n#print axioms entry{i}_checked\nend Bapa.PaxosEprLiteral\n")
 let imports := "import PaxosEprLiteralGlobal\n" ++ String.join ((List.range ps.length).map (fun i => s!"import PaxosEprLiteralEntry{i}\n"))
 let allExpr := names.foldr (fun n acc => "(entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family "++n++" && "++acc++")") "true"
 let checks := String.intercalate "," ((List.range ps.length).map (fun i => s!"entry{i}_checked"))
 let finish := "namespace Bapa.PaxosEprLiteral\nopen Kern Bapa.PaxosEprCountedGate\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ntheorem entries_checked : family.all (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family) = true := by\n change "++allExpr++" = true\n rw ["++checks++"]\n rfl\ntheorem family_checked : checkCMachine PaxosEprTarget.machine PaxosEprTarget.declarations family = true := combine _ _ _ global_checked entries_checked\ntheorem original_source_safety : ∀ ρ M, CReach PaxosEprAtomicSource.machine PaxosEprAtomicSource.declarations ρ M → PaxosEprAtomicSource.safety.Holds ρ (withCnt PaxosEprAtomicSource.declarations ρ M) := PaxosEprSafetyGate.source_from_checked_family family family_checked entries_exact\n#print axioms family_checked\n#print axioms original_source_safety\nend Bapa.PaxosEprLiteral\n"
 IO.FS.writeFile (out++"/PaxosEprAccepted.lean") (imports++finish))
end Bapa.PaxosEprLiteralExport
