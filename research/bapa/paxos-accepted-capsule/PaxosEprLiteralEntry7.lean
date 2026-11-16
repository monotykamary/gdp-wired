import PaxosEprLiteralLinks
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entry7_checked : entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry7 = true := by
 unfold entryGate
 rw [step7_checked]
 decide +kernel
#print axioms entry7_checked
end Bapa.PaxosEprLiteral
