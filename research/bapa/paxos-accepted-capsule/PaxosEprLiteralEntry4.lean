import PaxosEprLiteralFamily
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entry4_checked : entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry4 = true := by decide +kernel
#print axioms entry4_checked
end Bapa.PaxosEprLiteral
