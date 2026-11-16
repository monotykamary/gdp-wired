import PaxosEprLiteralLinks
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entry10_checked : entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry10 = true := by
 unfold entryGate
 rw [step10_checked]
 decide +kernel
#print axioms entry10_checked
end Bapa.PaxosEprLiteral
