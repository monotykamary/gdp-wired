import PaxosEprLiteralFamily
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entry5_checked : entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry5 = true := by decide +kernel
#print axioms entry5_checked
end Bapa.PaxosEprLiteral
