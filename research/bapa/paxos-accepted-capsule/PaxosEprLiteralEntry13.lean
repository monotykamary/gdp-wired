import PaxosEprLiteralFamily
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entry13_checked : entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry13 = true := by decide +kernel
#print axioms entry13_checked
end Bapa.PaxosEprLiteral
