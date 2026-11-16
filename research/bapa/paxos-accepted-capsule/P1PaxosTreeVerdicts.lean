import PaxosEprTreeRepairChecks
namespace Bapa.PaxosEprTreeRepairChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked_4 : candidateChecked 4 = true := by decide +kernel
#print axioms checked_4
theorem checked_5 : candidateChecked 5 = true := by decide +kernel
#print axioms checked_5
theorem checked_19 : candidateChecked 19 = true := by decide +kernel
#print axioms checked_19
theorem checked_21 : candidateChecked 21 = true := by decide +kernel
#print axioms checked_21
theorem checked_22 : candidateChecked 22 = true := by decide +kernel
#print axioms checked_22
end Bapa.PaxosEprTreeRepairChecks
