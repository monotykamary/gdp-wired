import PaxosEprTreesLinear10Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked_10 : Bapa.PaxosEprTreesLinear10Checks.candidateChecked 10 = true := by decide +kernel
#print axioms checked_10
