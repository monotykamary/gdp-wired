import PaxosEprLiteralFamily
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entry15_checked : entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry15 = true := by decide +kernel
#print axioms entry15_checked
end Bapa.PaxosEprLiteral
