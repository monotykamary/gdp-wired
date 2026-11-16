import PaxosEprTreesChecks
import PaxosEprTreesLinear20
namespace Bapa.PaxosEprTreesLinear20Checks
open Kern Cert Lean PaxosEprTreeRepairChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def build (i : Nat) : Except String (List C × List CDecl × CCert) := do
 let (g,ds,k) ← PaxosEprTreesChecks.build i
 return (g,ds,{k with tree := PaxosEprTreesLinear20.patched i k.tree})
def candidateChecked (i : Nat) : Bool :=
 match build i with | .ok (g,ds,k) => checkMC g ds k | .error _ => false

def failed (tab : List VDef) (hs : List C) (lemmas : List CutLemma) :
 Nat → List Bool → Path → Tree → List Json
 | 0,_,_,_ => []
 | fuel+1,dirs,p,.split r y n =>
   failed tab hs lemmas fuel (dirs++[true]) ((r,true)::p) y ++
   failed tab hs lemmas fuel (dirs++[false]) ((r,false)::p) n
 | _,dirs,p,t =>
   let p := lemmaPath lemmas p
   if checkT tab hs p t then [] else
   let es := PaxosEprTreesRepair.leafEqs t
   let next := (PaxosEprTreesRepair.missingTest tab hs p t).orElse
     (fun _ => hs.findSome? (PaxosEprTreesRepair.testC tab p))
   [Json.mkObj [("dirs",toJson dirs),("leaf",jt t),
    ("rows",jrs (leafRows tab p hs es)),("next",match next with | none => Json.null | some r => jr r)]]

def run : IO Unit := do
 let out := (← IO.getEnv "SUPERCOMPUTER_OUTPUT_DIR").getD "."
 let i := ((← IO.getEnv "PAXOS_LAW").bind String.toNat?).getD 20
 let (g,ds,k) ← match build i with | .error e => throw (IO.userError e) | .ok v => pure v
 let some hs := context ds k | throw (IO.userError "context absent")
 let checked := checkMC g ds k
 let f := if checked then [] else failed k.tab hs k.lemmas 1000 [] [] k.tree
 IO.FS.writeFile (out++"/LINEAR-FRONTIER.json")
  ((Json.mkObj [("law",jn i),("checked",toJson checked),("failed",ja f)]).compress++"\n")
end Bapa.PaxosEprTreesLinear20Checks
