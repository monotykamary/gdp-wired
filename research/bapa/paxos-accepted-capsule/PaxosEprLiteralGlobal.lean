import PaxosEprLiteralFamily
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem global_checked : globalGate PaxosEprTarget.machine PaxosEprTarget.declarations family = true := by decide +kernel
#print axioms global_checked
end Bapa.PaxosEprLiteral
