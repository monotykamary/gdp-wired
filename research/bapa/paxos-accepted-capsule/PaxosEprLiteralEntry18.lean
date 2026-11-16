import PaxosEprLiteralFamily
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entry18_checked : entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry18 = true := by decide +kernel
#print axioms entry18_checked
end Bapa.PaxosEprLiteral
