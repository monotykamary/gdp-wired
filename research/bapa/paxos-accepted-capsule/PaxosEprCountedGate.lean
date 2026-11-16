import PaxosEprSafetyGate
namespace Bapa.PaxosEprCountedGate
open Kern

def globalGate (s : SMachine) (ds : List CDecl) (ps : List CEntry) : Bool :=
 sOk s && avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) s.f.m.pre && !readsC s.f.m.pre
 && sTermsOk s (flagVars s.f.flags) && factsOk s && cDistinct (cMaps ds ++ cPosts ds)
 && cApart s ds && ds.all (cDeclOk s ds (ps.map (·.e)))

def entryGate (s : SMachine) (ds : List CDecl) (ps : List CEntry) (ce : CEntry) : Bool :=
 cEntryOk s ds (ps.map (·.e)) ce.e && witsOk s (ps.map (·.e)) ce.start && witsOk s (ps.map (·.e)) ce.step
 && checkMC (cStartGoal s ds ce.e) (cStartDecls s ds) ce.start
 && checkMC (cStepGoal s ds (ps.map (·.e)) ce.e) (cStepDecls s ds) ce.step

theorem combine (s : SMachine) (ds : List CDecl) (ps : List CEntry)
 (hg : globalGate s ds ps = true) (he : ps.all (entryGate s ds ps) = true) : checkCMachine s ds ps = true := by
 change (globalGate s ds ps && ps.all (entryGate s ds ps)) = true
 rw [hg,he]
 rfl
#print axioms combine
end Bapa.PaxosEprCountedGate
