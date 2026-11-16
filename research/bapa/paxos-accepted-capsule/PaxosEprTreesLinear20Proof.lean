import PaxosEprTreesLinear20Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked_20 : Bapa.PaxosEprTreesLinear20Checks.candidateChecked 20 = true := by decide +kernel
#print axioms checked_20
