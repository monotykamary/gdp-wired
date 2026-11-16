import PaxosEprLiteralFamily
import PaxosEprTreesLinear7Proof
import PaxosEprTreesLinear10Proof
import PaxosEprTreesLinear20Proof
namespace Bapa.PaxosEprLiteral
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0
deriving instance DecidableEq for CInst, CutLemma, CCert

theorem link7 : PaxosEprTreesLinear7Checks.build 7 = .ok
 (cStepGoal PaxosEprTarget.machine PaxosEprTarget.declarations (family.map (·.e)) entry7.e,
 cStepDecls PaxosEprTarget.machine PaxosEprTarget.declarations,entry7.step) := by decide +kernel

theorem link10 : PaxosEprTreesLinear10Checks.build 10 = .ok
 (cStepGoal PaxosEprTarget.machine PaxosEprTarget.declarations (family.map (·.e)) entry10.e,
 cStepDecls PaxosEprTarget.machine PaxosEprTarget.declarations,entry10.step) := by decide +kernel

theorem link20 : PaxosEprTreesLinear20Checks.build 20 = .ok
 (cStepGoal PaxosEprTarget.machine PaxosEprTarget.declarations (family.map (·.e)) entry20.e,
 cStepDecls PaxosEprTarget.machine PaxosEprTarget.declarations,entry20.step) := by decide +kernel

theorem step7_checked : checkMC
 (cStepGoal PaxosEprTarget.machine PaxosEprTarget.declarations (family.map (·.e)) entry7.e)
 (cStepDecls PaxosEprTarget.machine PaxosEprTarget.declarations) entry7.step = true := by
 have h := checked_7
 unfold PaxosEprTreesLinear7Checks.candidateChecked at h
 rw [link7] at h
 exact h

theorem step10_checked : checkMC
 (cStepGoal PaxosEprTarget.machine PaxosEprTarget.declarations (family.map (·.e)) entry10.e)
 (cStepDecls PaxosEprTarget.machine PaxosEprTarget.declarations) entry10.step = true := by
 have h := checked_10
 unfold PaxosEprTreesLinear10Checks.candidateChecked at h
 rw [link10] at h
 exact h

theorem step20_checked : checkMC
 (cStepGoal PaxosEprTarget.machine PaxosEprTarget.declarations (family.map (·.e)) entry20.e)
 (cStepDecls PaxosEprTarget.machine PaxosEprTarget.declarations) entry20.step = true := by
 have h := checked_20
 unfold PaxosEprTreesLinear20Checks.candidateChecked at h
 rw [link20] at h
 exact h
#print axioms link7
#print axioms link10
#print axioms link20
#print axioms step7_checked
#print axioms step10_checked
#print axioms step20_checked
end Bapa.PaxosEprLiteral
