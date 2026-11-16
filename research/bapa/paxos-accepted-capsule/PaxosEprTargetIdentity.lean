import PaxosEprTargetDefs
import PaxosEprAdapterAudit
namespace Bapa.PaxosEprTarget
open Kern
deriving instance DecidableEq for E, C
deriving instance DecidableEq for Except
deriving instance DecidableEq for MLaw, MMachine, FMMachine, SMachine, CDecl
deriving instance DecidableEq for RadixKeySyntax.Error, PaxosEprPrefixTail.Error, PaxosEprAdapterSyntax.Error
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Reification is checked by reduction, not trusted as a new machine. -/
theorem machine_exact : PaxosEprAdapterAudit.targetMachine = .ok machine := by decide +kernel
theorem declarations_exact : PaxosEprAdapterAudit.targetDecls = .ok declarations := by decide +kernel
#print axioms machine_exact
#print axioms declarations_exact
end Bapa.PaxosEprTarget
