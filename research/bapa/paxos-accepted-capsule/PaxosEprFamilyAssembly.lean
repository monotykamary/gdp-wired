import PaxosEprSafetyGate
import PaxosEprKindRepair
import PaxosEprTreesRepair
import PaxosEprTree24Frozen
import PaxosEprTreesLinear
import PaxosEprTreesLinear7
import PaxosEprTreesLinear10
import PaxosEprTreesLinear20
import PaxosEprTreesLinear23
namespace Bapa.PaxosEprFamilyAssembly
open Kern Bapa.PaxosEprTreeRepairChecks

/-- Only positively checked incoming tree handoffs are installed. The other
steps are accepted only after the unified full counted gate checks. -/
def installedTrees : List Nat := [7,9,10,13,14,15,16,18,20,23,24]
def pendingSteps : List Nat := []

def repairStep (i : Nat) (goal : List C) (ds : List CDecl) (k : CCert) : Except String CCert :=
 if [1,2,3].contains i then PaxosEprKindRepair.repair i goal k
 else if [4,5,19,21,22].contains i then PaxosEprTreeRepair.repair i goal ds k
 else if i == 12 then PaxosEprRow12Repair.repair i goal k
 -- This snapshot previously passed both STEP13 and STEP24 in assembly-2.
 else if [13,24].contains i then PaxosEprTree24Frozen.repair i goal ds k
 else if i == 7 then PaxosEprTreesLinear7.repair i goal ds k
 else if i == 9 then PaxosEprTreesLinear.repair i goal ds k
 else if i == 10 then PaxosEprTreesLinear10.repair i goal ds k
 else if i == 20 then PaxosEprTreesLinear20.repair i goal ds k
 else if i == 23 then PaxosEprTreesLinear23.repair i goal ds k
 else if installedTrees.contains i then PaxosEprTreesRepair.repair i goal ds k
 else .ok k

def buildCerts (allEs : List SEntry) (i : Nat) (old : CEntry) (e : SEntry) : Except String (CCert × CCert) := do
 let s := PaxosEprTarget.machine
 let ds := PaxosEprTarget.declarations
 let ns ← (PaxosEprAdapterNamed.hypotheses profiles source s oldDecls ds (retained.map (·.e)) allEs old.e e false old.start).mapError (fun e => reprStr e)
 let nt ← (PaxosEprAdapterNamed.hypotheses profiles source s oldDecls ds (retained.map (·.e)) allEs old.e e true old.step).mapError (fun e => reprStr e)
 let start ← (PaxosEprAdapterCertificate.certificate config old.start (some ns)).mapError (fun e => reprStr e)
 let step ← (PaxosEprAdapterCertificate.certificate config old.step (some nt)).mapError (fun e => reprStr e)
 let repaired ← repairStep i (cStepGoal s ds allEs e) (cStepDecls s ds) step
 return (start,repaired)

def assembleEntries (allEs : List SEntry) : List CEntry → List SEntry → Nat → Except String (List CEntry)
 | [],[],_ => .ok []
 | old::olds,e::es,i =>
    match buildCerts allEs i old e with
    | .error err => .error err
    | .ok pair => match assembleEntries allEs olds es (i+1) with
      | .error err => .error err
      | .ok rest => .ok (⟨e,pair.1,pair.2⟩ :: rest)
 | _,_,_ => .error "retained/target entry count mismatch"

theorem assembleEntries_preserves (allEs : List SEntry) (olds : List CEntry)
 (es : List SEntry) (i : Nat) {ps : List CEntry}
 (h : assembleEntries allEs olds es i = .ok ps) : ps.map (·.e) = es := by
 induction olds generalizing es i ps with
 | nil =>
   cases es <;> simp [assembleEntries] at h
   subst ps
   rfl
 | cons old olds ih =>
   cases es with
   | nil => simp [assembleEntries] at h
   | cons e es =>
     cases ha : buildCerts allEs i old e with
     | error err => simp [assembleEntries,ha,Except.bind] at h
     | ok pair =>
       cases hb : assembleEntries allEs olds es (i+1) with
       | error err => simp [assembleEntries,ha,hb,Except.bind] at h
       | ok rest =>
         simp [assembleEntries,ha,hb,Except.bind] at h
         subst ps
         simp only [List.map_cons]
         rw [ih es (i+1) hb]

def buildFamily : Except String (List CEntry) :=
 match targetEntries with
 | .error err => .error err
 | .ok es => assembleEntries es retained es 0

theorem family_entries_exact {ps : List CEntry} (h : buildFamily = .ok ps) :
 targetEntries = .ok (ps.map (·.e)) := by
 cases he : targetEntries with
 | error err => simp [buildFamily,he,Except.bind] at h
 | ok es =>
   have hs : assembleEntries es retained es 0 = .ok ps := by simpa [buildFamily,he,Except.bind] using h
   have hm := assembleEntries_preserves es retained es 0 hs
   rw [hm]

/-- Check the exact shared per-entry constructor against the full frozen law
context, without reducing every unrelated certificate repair first. The final
family acceptance still requires checkCMachine on buildFamily's whole result. -/
def checkedAt (i : Nat) (step : Bool) : Bool := match targetEntries with
 | .error _ => false
 | .ok es => match retained[i]?,es[i]? with
   | some old,some e => match buildCerts es i old e with
     | .error _ => false
     | .ok pair => if step then checkMC (cStepGoal PaxosEprTarget.machine PaxosEprTarget.declarations es e)
         (cStepDecls PaxosEprTarget.machine PaxosEprTarget.declarations) pair.2
       else checkMC (cStartGoal PaxosEprTarget.machine PaxosEprTarget.declarations e)
         (cStartDecls PaxosEprTarget.machine PaxosEprTarget.declarations) pair.1
   | _,_ => false

/-- Final assembled source theorem, conditional on the actual complete gate.
No list of partial receipts is promoted to that premise. -/
theorem source_from_assembly {ps : List CEntry} (h : buildFamily = .ok ps)
 (hc : checkCMachine PaxosEprTarget.machine PaxosEprTarget.declarations ps = true) :
 ∀ ρ M, CReach PaxosEprAtomicSource.machine PaxosEprAtomicSource.declarations ρ M →
 PaxosEprAtomicSource.safety.Holds ρ (withCnt PaxosEprAtomicSource.declarations ρ M) :=
 PaxosEprSafetyGate.source_from_checked_family ps hc (family_entries_exact h)

#print axioms assembleEntries_preserves
#print axioms family_entries_exact
#print axioms source_from_assembly
end Bapa.PaxosEprFamilyAssembly
