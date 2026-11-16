import PaxosEprLiteralFamily
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entry21_checked : entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry21 = true := by decide +kernel
#print axioms entry21_checked
end Bapa.PaxosEprLiteral
