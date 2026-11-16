import PaxosEprLiteralFamily
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entry8_checked : entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry8 = true := by decide +kernel
#print axioms entry8_checked
end Bapa.PaxosEprLiteral
