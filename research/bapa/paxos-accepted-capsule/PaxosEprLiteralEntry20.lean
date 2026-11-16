import PaxosEprLiteralLinks
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entry20_checked : entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry20 = true := by
 unfold entryGate
 rw [step20_checked]
 decide +kernel
#print axioms entry20_checked
end Bapa.PaxosEprLiteral
