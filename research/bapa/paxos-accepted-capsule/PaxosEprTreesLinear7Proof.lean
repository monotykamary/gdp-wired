import PaxosEprTreesLinear7Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked_7 : Bapa.PaxosEprTreesLinear7Checks.candidateChecked 7 = true := by decide +kernel
#print axioms checked_7
