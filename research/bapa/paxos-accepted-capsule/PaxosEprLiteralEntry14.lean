import PaxosEprLiteralFamily
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entry14_checked : entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry14 = true := by decide +kernel
#print axioms entry14_checked
end Bapa.PaxosEprLiteral
